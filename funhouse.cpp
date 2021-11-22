//============================================================================
// Name        : fun-house_mirror.cpp
// Author      : Peter Che
// Version     :
// Copyright   : Peter Che 7210208@gmail.com
// Description : Pet Project in C
//============================================================================

/*
 * программа должна делать следующее
 * 1. Запускается несколько потоков для обработки
 * 2. Каждый поток ждет соединения и получает FastCGI данные с помощью библиотеки
 * 3. Каждый поток парсит заголовки
 *    и либо получает и сохраняет файл из потока FastCGI,
 *    либо забирает сохраненный файл картинки с диска.
 * 4. Получив файл-картинку поток вызывает для обработки
 *    OpenCV.
 * 5. Считывает картинку себе в память. Если большая, то resize
 * 6. если нажата одна из кнопок "нравится"/"отказать", то получает
 *    из запроса старые значения обработки и сохраняет ответ в файл.
 * 7.   Случайным образом (тоже вариант ) генерит новые параметры
 * 8. поток расчитывает параметры remap (три варианта)
 * 9. поочередно применяет все три remap и получает выходную картинку
 * 10. выходную картинку сохраняет на диск и с помощью scp отправляет на сервер 10.0.1.1 (FreeBSD)
 * 11. создает соответствующую  HTML страницу и отправляет её
 *     на внешний сервер
 * 12. Записывает в журнал параметры обработки, имя файла, время обработки.
 */

#include <errno.h>

#include <unistd.h>
#include <pthread.h>
#include <sys/types.h>
#include <stdio.h>
#include <string.h>
#include "math.h"
#include <fcntl.h>
#include <time.h>       /* time_t, struct tm, time, localtime */

#include "fcgi_config.h"
#include "fcgiapp.h"

#include "opencv2/core/utility.hpp"
#include "opencv2/imgproc.hpp"
#include "opencv2/imgcodecs.hpp"
#include "opencv2/core/mat.hpp"

#include <openssl/sha.h>

using namespace cv;
using namespace std;

// определяем длину разных буферов
// для имени файла, для имени и пути,
// для одной записи в журнал. Т.е. вся инфо для журнала заносится в переменную
// и только после выполнения всех операций заносится в журнал
//
// debug и log это разные операции
// отладку нужно вкоде испоотзовать с инструкциями препроцессора
//
#define BUFLEN_F NAME_MAX + 1024
#define BUFLEN_TXT PATH_MAX + NAME_MAX
#define LOG_TXT_LEN PATH_MAX + NAME_MAX + 1024
#define THREAD_COUNT 4 					// количество потоков.

// адрес внешнего сервера.
#define FRONT_ADDR "107.189.8.250"
// внутренний адрес
// лучше конечно вынести их в параметры для этой программы
// будет лучше и  наглядней
#define SOCKET_PATH "192.168.0.66:8888"

// условные названия ошибок
// лучше избегать констант типа ошибка номер "9" в коде
// лучше дефайнить
//
#define ERROR_OPEN_TEMP_FILE 1 			//Error open temporary data file
#define ERROR_ACCEPT_NEW_REQUEST 2 		//Error accept new request
#define ERROR_IMAGE_ZERO_DIMENSION 3
#define ERROR_FILE_NAME 4
#define REQUEST_FORMAT_ERROR_0 5 		// REQUEST_FORMAT_ERROR
#define REQUEST_CONTENTLENGHT_ERROR 6 	//
#define REQUEST_GETSTR_ERROR 7 			//
#define REQUEST_BOUNDARY_ERROR 8 		//
#define REQUEST_FILENAME_NOTFOUND 9 	//
#define REQUEST_FILENAME_ERROR 10 		//
#define REQUEST_FORMAT_ERROR_6 11 		//
#define REQUEST_CONTENTTYPE_ERROR 12 	//
#define REQUEST_FILETYPE_ERROR 13 		//
#define REQUEST_FORMAT_ERROR_RD 14 		//
#define REQUEST_SERVER_NAME_ERROR 15 	// SERVER_NAME_FORMAT_ERROR
#define ERROR_RENAME_TMPFILE 101
#define READ_FILE_EXEPTION 102 			//read file exception
#define WRITE_FILE_EXEPTION 103
#define ERROR_TRANFER_RES_FILE 104
#define ERROR_FASTCGI_SEND 105
#define ERROR_ 105

#define SALT_LEN 3

// количество параметров обработки изображений
// в этои варианте все 12 не используются
//
#define PARAMETERS_NUM 12

#define MAX_IMAGE_ROWS 512
#define MAX_IMAGE_COLS 512
#define MIN_IMAGE_ROWS 16
#define MIN_IMAGE_COLS 16

// условные названия параметров
// т.е. в массиве param под номером ANGLE_0 будет 0
// так сделано для наглядности
// если поменять количество параметров,
// что то же что и размер массива param, то
// формирование HTML страницы не изменится, поменяется только обработка
#define ANGLE_0 0
#define ANGLE_1 1
#define ANGLE_2 2

#define PERIOD_0 3
#define PERIOD_1 4
#define PERIOD_2 5

#define AMPLITUDE_0 6
#define AMPLITUDE_1 7
#define AMPLITUDE_2 8

#define SIGN_0 9
#define SIGN_1 10
#define SIGN_2 11

//хранит дескриптор открытого сокета
static int socketId;
// наличие нескольких потоков требует всегда внимания
// и мьютексы позволят избежать одновременного использования
//  общих данных в разных потоках
static pthread_mutex_t accept_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t log_mutex = PTHREAD_MUTEX_INITIALIZER;

FILE *log_file;
FILE *marks_file;

// вспомогательный код
//возвращает или 1 или 0 или -1
// с равной вероятностью
// для выбора параметров обработки
// если всё по нулям, то вернется исходная картинка
float rand_101(void) {
	float ret = float(rand() % 6);
	if (ret < 2.)
		return (0.);
	else if (ret < 4.)
		return (-1.);
	return (1.);
}

// кодирование строки. Следующая программа делает обратное преобразование
// кодировка base64 не годится для пребразования в HTML код и обратно
// а base58, как часть библитеки биткойн, не смог запустить ((
void char2hex(char *hex, char *src, size_t src_len) {
	size_t i;
	uchar t;

	for (i = 0; i < src_len; i++) {
		t = (uchar) src[i] & 0xff;
		hex[i * 2] = (uchar) ((uchar) ((t & 0x0f)) + 65);
		hex[2 * i + 1] = (uchar) ((uchar) (((t >> 4) & 0x0f)) + 65);
	}
}

void hex2char(const char *hex, char *src, size_t src_len) {
	size_t i;

	for (i = 0; i < src_len; i++)
		src[i] = (uchar) ((uchar) ((hex[i * 2 + 1] - 65) << 4)
				+ (uchar) (hex[i * 2] - 65));
}

static void* do_thread(void *thread_num) {

// переменная для хранения кода ошибки
// коды ошибок в дефайнах
	int error_idx;
// переменная для хранения кода возврата разных функций
	int ret;
// переменная для хранения номера потока
	int thread_idx;
//
	FCGX_Request request;

// тут хранится название рабочего файла в который будет приниматься картинка
	char tmp_file_name[22] = "data/tmp/  fcgi.bin";
// буфер для приема данных из сокета fastcgi
	char buffer[BUFLEN_F + 1];
// переменные для разбора вложения в fastcgi запрос
	char *buf_start;
	char *buf_end;
	char *buf_current; // current point in buffer
// переменные из запроса fastcgi
	char *server_name;
	char *boundary;
	char *content_type;
	char *request_method;
	char *script_name;
	char *ch_content_len;
// размер содержимого lighttpd присылает в символьном виде
// и нужно перекодировать в int
	int content_len;
	int file_len;
// имя файла из запроса
	char file_name[NAME_MAX];
// путь к файлу картинки
	char file_path[PATH_MAX + NAME_MAX];
	char file_type[NAME_MAX];
	char out_file_path[PATH_MAX];

// буфер для формирования команды scp
	char exec_txt[BUFLEN_TXT];
// буфер для формирования страниц HTML
	char html_txt[BUFLEN_TXT];
// буфер для формирования ответа в виде fcgi
	char fcgi_txt[BUFLEN_TXT];
// буфер для преобразования кодировок
	char hex_txt[BUFLEN_TXT];
// буфер для формирования записи в журнал
// запись формируется и в конце обработки запроса отправляется в журнал
// для отладки не годится
// если вдруг станете переделывать, что везде где формируется журнал,
// сразу пишите в stdout.
// если будет ошибка и программа вылетит, то в журнале о последнем запросе ничего не будет
	char log_txt[LOG_TXT_LEN];

// буфер для формирования хэш
	unsigned char md_buf[SHA256_DIGEST_LENGTH];
// служебные переменные
	char *t_pointer;
	int i, j;
	float scale;

// служебные переменные для преобразования картинок
	float row, col, row2, col2, row1, col1, f_i, f_j, angle_i, angle_j;
// в img_origin может поступить большая картинка и её возможно придется
// ресайзить.В img_in находится картинка для дальнейшей обработки
	Mat img_in, img_origin;
	int img_width;

// массив параметров преобразования картиники
// этот массив отправляется в HTML запросе и в ответе кодируется
// вместе с именем файла+соль.
// это доп функциональ, для учета ответов на показ обработанных картинок
	float param[PARAMETERS_NUM];
	unsigned char salt;
	float tt;			// переменная для промежуточных вычислений

	char *first_point;
	int batchRW;
	int done;

	int tmp_fd;

// http://all-ht.ru/inf/prog/c/func/localtime_r.html
//Переменная для сохранения текущего системного времени
	long int s_time;
//Структура, в который будет помещен результат преобразования времени
	struct tm m_time;
//Буфер, в который будет записана текстовая строка времени
	char time_buf[26];


	thread_idx = *((int*) thread_num);

// инициализируем запрос к сокету
	if (FCGX_InitRequest(&request, socketId, 0) != 0) {
		//ошибка при инициализации структуры запроса
		fprintf(log_file, " thread %d. Can not initializing request\n",
				thread_idx);
		return NULL;
	}

// сокет открыт и ждем поступления данных
	for (;;) {

// начальная инициализация переменных
// все буферные переменные обнуляются
		error_idx = 0;
		bzero(log_txt, LOG_TXT_LEN);
		bzero(file_name, NAME_MAX);
		bzero(file_path, PATH_MAX + NAME_MAX);
		bzero(file_type, NAME_MAX);
		bzero(out_file_path, PATH_MAX);
		bzero(exec_txt, BUFLEN_TXT);
		bzero(html_txt, BUFLEN_TXT);
		bzero(fcgi_txt, BUFLEN_TXT);
		bzero(hex_txt, BUFLEN_TXT);
		bzero(log_txt, LOG_TXT_LEN);
		bzero(time_buf, 26);

		do {
// фиксирует время начала и записываем в log_txt который
// в конце цикла будет отправлен в файл журнала
			s_time = time(NULL);
			localtime_r(&s_time, &m_time);
			sprintf(log_txt + strlen(log_txt), " thread %d. time %s",
					thread_idx, asctime_r(&m_time, time_buf));
			sprintf(tmp_file_name, "%s%03d%s", "data/tmp/", thread_idx,
					"fcgi.bin");
// открываем временный файл в имени которого номер потока
// многопоточность это очень важно и это нужно всегда учитывать
// хоть и не всегда есть уверенность в правильности
//
// временный файл открываем до начала открытия сокета
// так задумано, что бы вынести дорогую операцию создания файла вне цикла обработки
			tmp_fd = open(tmp_file_name, O_WRONLY | O_CREAT | O_TRUNC, 0644);
			if (tmp_fd < 3) {
				sprintf(log_txt + strlen(log_txt), "\t%s %s.\n",
						"Error open temporary data file", tmp_file_name);
// если не смогли открыть рабочий файл, значит система больна
// и нет возможности принимать данные через сокет
// и нет смысла ждать соединение
				error_idx = ERROR_OPEN_TEMP_FILE;
				continue;
			}
// заполняем переменную журнала информацией
			sprintf(log_txt + strlen(log_txt),
					"\tdata file %s opened\n\tTry to accept new request\n",
					tmp_file_name);

// попробуем получить FastCGI запрос
// на обработку.
// Другие потоки ждут освобождения
// как только этот поток получит соединение
// то следующий по очереди поток становится в ожидание соединения
			pthread_mutex_lock(&accept_mutex);
			ret = FCGX_Accept_r(&request);
			pthread_mutex_unlock(&accept_mutex);

			if (ret < 0) {
// ошибка при получении запроса
// продолжаем цикл
				fprintf(log_file, " thread %d. Error accept new request\n",
						thread_idx);
				fflush(log_file);
				error_idx = ERROR_ACCEPT_NEW_REQUEST;
				continue;
			}
// получили через сокет запрос FastCGI
// сохраняем параметры запроса и определяем
// содержит ли запрос файл или это только ответ на вопрос
			server_name = FCGX_GetParam("SERVER_NAME", request.envp);
			content_type = FCGX_GetParam("CONTENT_TYPE", request.envp);
			ch_content_len = FCGX_GetParam("CONTENT_LENGTH", request.envp);
			content_len = atoi(ch_content_len);
			request_method = FCGX_GetParam("REQUEST_METHOD", request.envp);
			script_name = FCGX_GetParam("SCRIPT_NAME", request.envp);

// проверяем, пришел ли FastCGI запрос с нашего внешнего сервера?
// или это чья то шутка
			if (strncmp(server_name, FRONT_ADDR, strlen(FRONT_ADDR))) {
				error_idx = REQUEST_SERVER_NAME_ERROR;
				continue;
			}

// поля должны быть заполнены или это ошибка
			if (!(server_name and request_method and script_name)) {
				error_idx = REQUEST_FORMAT_ERROR_0;
				continue;
			}

// далее обработка запроса содержащего вложение
// т.е. запрос содержит не нулевой длины вложение
// и его нужно распарсить и извлечь файл
			if (content_len != 0) {
// определяем разделитель. Это достаточно случайный текст, который служит разделителем
// в теле запроса
				boundary = strcasestr(content_type, "boundary=")
						+ strlen("boundary=");
				if ((content_len <= 100) or (content_len >= 10000000)) {
// если содержимое мало или велико, то ничего не делаем и начинаем новый цикл
// размер выбран произвольно и вот таких констант в цифровом в коде
// быть не должно и если будете адаптировать себе,
// то обязательно поменяйте
					error_idx = REQUEST_CONTENTLENGHT_ERROR;
					continue;
				}
// считываем с сокета первый буфер и сохраняем длину считаного в batchRW
				batchRW = FCGX_GetStr(buffer, BUFLEN_F, request.in);
				if (batchRW <= 0) {
					error_idx = REQUEST_GETSTR_ERROR;
					break;
				}
// ищем boundary в запросе. Вся инфо после него
				if ((buf_start = strcasestr(buffer, boundary)) == NULL) {
					error_idx = REQUEST_BOUNDARY_ERROR;
					break;
				}
				buf_start += strlen(boundary);

// ищем слово "filename=" в запросе
				if ((buf_current = strcasestr(buf_start, "filename=")) == NULL) {
					error_idx = REQUEST_FILENAME_NOTFOUND;
					break;
				}
				buf_current += strlen("filename=");
// теперь buf_current указывает на первый байт после "filename="
// и надеемся, что это имя файла
				if (*(buf_current++) != '"')
// название файла в кавычках. Это открывающая
						{
					error_idx = REQUEST_FILENAME_ERROR;
					break;
				}
// поиск закрывающей кавычки до конца buffer
// то, что в кавычках после "filename=" и есть имя файла во вложении
				buf_end = (char*) memchr(buf_current, '"',
						batchRW - 2 * strlen(boundary));
				bzero(file_name, NAME_MAX);
// проверяем имя файла на длину
// т.к. далее к имени файла будем приписывать 3 байта номер потока и соль,
// то файлы с очень длинным именем не обрабатываем
// можно сохранить имя файла в таблицу и там же сопоставить имя файла внутри
// и хранить под этим имененм
// но это еще много кода и новая сущность
				if (buf_end - buf_current
						>= (int) (NAME_MAX - SALT_LEN - 3)
						or buf_end - buf_current <= 4) {
					error_idx = REQUEST_FILENAME_ERROR;
					break;
				}
// вот тут мы выделили из запроса имя файла

				t_pointer = file_name;
// к имени файла приписывам соль, что бы имена не повторялись.
// если поступят на обработку в одном и том же потоке два файла с одинаковым именем,
// то отличаться они будут на соль
// если совпадут номер потока, имя файла и соль - это катастрофа всего миропорядка
				for (i = 0; i < SALT_LEN; i++) {
					salt = rand() % 256;
					char2hex(t_pointer, (char*) &salt, sizeof(salt));
					t_pointer += 2 * sizeof(salt);
				}
				memcpy(t_pointer, buf_current, buf_end - buf_current);
// выделяем из запроса тип вложения
				if ((buf_current = strcasestr(buf_start, "Content-Type: "))
						== NULL) {
					error_idx = REQUEST_CONTENTTYPE_ERROR;
					break;
				}
				buf_current += strlen("Content-Type: ");
// поиск закрывающего 0d 0a до конца buffer
				buf_end = (char*) memchr(buf_current, 0x0d, batchRW);
// имя файла и служебная информация заведомо поместятся в буфер
// ну или должны поместиться. Так выбирали размер буфера для чтения

				bzero(file_type, NAME_MAX);
				if (buf_end - buf_current >= NAME_MAX
						or buf_end - buf_current == 0) {
					error_idx = REQUEST_FILETYPE_ERROR;
					break;
				}
				memcpy(file_type, buf_current, buf_end - buf_current);

				if (strncmp(buf_end, "\r\n\r\n", 4) != 0) {
					error_idx = REQUEST_FORMAT_ERROR_RD;
					break;
				}
				buf_start = buf_end + 4;
// 2 is fin boundary '--' 6 if first 2d2d2d2d2d2d
// размер вложения включает длину файла и длину служебной информации
// размер вложения без служебной информации и есть длина файла.
				file_len = content_len - (buf_start - buffer) - strlen(boundary)
						- 2 - 6;
				done = file_len;
// формат заголовка и его парсинг вызывают сомнения.
// но библитеку такую не нашел, что бы сразу распарсить и файлы сохранить
// почилось кривовато, работает, но наверно есть лучше решение

// всё, что осталось в буфере это часть файла
// который записываем в служебный, заранее открытый файл
				batchRW = batchRW - (buf_start - buffer);
// и по частям получаем из сокета данные и пишем в файл
// длину получили заранее
// если браузер прислал два и более файлов, то принимается только один.

// если запись файла невозможна,значит нет места или мир рухнул
// можно выйти по continue  и начать цикл обработки заново и ждать
// пока не появится место
				if (file_len <= batchRW) {
					ret = write(tmp_fd, buf_start, file_len);
					done = 0;
				} else {
					ret = write(tmp_fd, buf_start, batchRW);
					done -= batchRW;
				}
				if (ret < 0) {
					error_idx = WRITE_FILE_EXEPTION;
					break;
					}
				while (done > 0) {
// вот тут следующий кусок файла получаем
					batchRW = FCGX_GetStr(buffer, BUFLEN_F, request.in);
					if (batchRW <= 0)
						break;
					if (done <= batchRW) {
						ret = write(tmp_fd, buffer, done);
						done = 0;
						break;
					} else {
						ret = write(tmp_fd, buffer, batchRW);
						done -= batchRW;
					}
					if (ret < 0) {
						error_idx = WRITE_FILE_EXEPTION;
						break;
						}
				}
				if (ret < 0) {
					error_idx = WRITE_FILE_EXEPTION;
					break;
					}

// вот тут файл получили, сохранили в папку data/images/ под рабочим названием
// и можно его скормить напрмер OpenCV
				close(tmp_fd);

				bzero(file_path, PATH_MAX + NAME_MAX);
				errno = 0;
				if (strlen(file_name) > 0) {
					memcpy(file_path, "data/images/", 12);
					memmove(file_path + 12, file_name, strlen(file_name));
					if ((ret = rename(tmp_file_name, file_path)) < 0) {
// переименовываем файл. Рабочее название свободно и файл теперь записан под тем именем
// что пришел + соль + номер потока
						error_idx = ERROR_RENAME_TMPFILE;
						break;
					}
				}
			} else {
// если в fastCGI запросе нет вложений. Значит это ответ на вопрос.
// в ответе содержится имя файла, значения параметров и ответ на вопрос
// Всё можно извлечь и сохранить в файл marks
// и передать имя файла (а он в исходном виде сохранен) на новую обработку
// тут можно еще проверок добавить разных и нужных
				bzero(fcgi_txt, BUFLEN_TXT);
				first_point = strchr(script_name, '.');
				hex2char((char*) (script_name + 1), fcgi_txt,
						(size_t) (first_point - script_name - 1) / 2);
				bzero(file_name, NAME_MAX);
				strcpy(file_name,
						fcgi_txt + SHA256_DIGEST_LENGTH
								+ PARAMETERS_NUM * sizeof(param[ANGLE_1])
								+ SALT_LEN * sizeof(salt));
				bzero(file_path, PATH_MAX + NAME_MAX);
				memcpy(file_path, "data/images/", 12);
				memmove(file_path + 12, file_name, strlen(file_name));
				memcpy(param, fcgi_txt + SHA256_DIGEST_LENGTH,
				PARAMETERS_NUM * sizeof(param[ANGLE_1]));

// извлекаем ответ из запроса
				if (strncmp(first_point + 1, "yes", 3) == 0)
					fprintf(marks_file, "%s", "yes");
				else
					fprintf(marks_file, "%s", "no");
// сохраняем параметры
				fprintf(marks_file, "\t%s", file_name);
				for (i = 0; i < PARAMETERS_NUM; i++) {
					sprintf(log_txt + strlen(log_txt),
							"\treceived parameter_%0d=%f\n", i, param[i]);
					fprintf(marks_file, "\t%f", param[i]);
				}
				fprintf(marks_file, "\n");
				fflush(marks_file);
			}

		} while (0);
// записываем в переменную параметры запроса
		sprintf(log_txt + strlen(log_txt), "\tserver name -  %s \n",
				server_name);
		sprintf(log_txt + strlen(log_txt), "\tcontent_type   %s \n",
				content_type);
		sprintf(log_txt + strlen(log_txt), "\tcontent length %d \n",
				content_len);
		sprintf(log_txt + strlen(log_txt), "\trequest_method %s \n",
				request_method);
		sprintf(log_txt + strlen(log_txt), "\tscript name    %s \n",
				script_name);
		sprintf(log_txt + strlen(log_txt), "\tContent-Type:  %s \n", file_type);
		sprintf(log_txt + strlen(log_txt), "\tfile_name      %s \n", file_name);

// если не было ошибок и всё в порядке
// то тут есть файл - или только полученный или сохраненный ранее
		while (error_idx == 0 and strlen(file_name) > 0) {
//                          ...
// запускаем обработку OpenCV
// если вдруг захотите применить свою обработку. Наверно захотите.
// то вот в это место и нужно вставлять свой код
// в filename строка с именем скачанного файла
//
// фиксируем время начала обработки
			s_time = time(NULL);
			localtime_r(&s_time, &m_time);
			sprintf(log_txt + strlen(log_txt), "\topencv start time %s",
					asctime_r(&m_time, time_buf));

// считываем файл в пямять
// можно, конечно для скорости, вновь полученный файл целиком сохранять в памяти
// и тут определить тип и использовать библиотеки без OpenCV
// или подать на вход imread  файл из памяти
// а файл сохранить после отправки ответа за запрос.
// можно
			try {
				img_origin = imread(file_path, IMREAD_COLOR);
// исключение OpenCV нужно обрабатывать
// файл могут прислать бажный
			} catch (cv::Exception &e) {
				const char *err_msg = e.what();
				fprintf(log_file,
						" thread %d. read file exception caught: %s \n ",
						thread_idx, err_msg);
				fflush(log_file);
				error_idx = READ_FILE_EXEPTION;
				continue;
			}
// маленькие картинки не обрабатываем
// к сожалению OpenCV файлы формата .heif
// определяет как файлы с нулевой размерностью
// поэтому размер файла и размер картинки это разные вещи
			if (img_origin.rows < MIN_IMAGE_ROWS
					or img_origin.cols <= MIN_IMAGE_COLS) {
				error_idx = ERROR_IMAGE_ZERO_DIMENSION;
// .heif not supported https://github.com/opencv/opencv/issues/14534
				continue;
			}
// большие картинки сжимаем
// можно добавить проверку MAX_IMAGE_ROWS и MAX_IMAGE_COLS
// есди один из них равен 0, то ничего не делаем
			if (img_origin.rows >= MAX_IMAGE_ROWS
					or img_origin.cols >= MAX_IMAGE_COLS) {

				scale = MIN(float(img_origin.rows)/MAX_IMAGE_ROWS,
						float(img_origin.cols)/MAX_IMAGE_COLS);
				resize(img_origin, img_in,
						Size(int(float(img_origin.cols) / scale),
								int(float(img_origin.rows) / scale)),
						INTER_LINEAR);
			} else
				img_in = img_origin;

// тут делаем несколько предварительных вычислений
// эта часть исключительно простого преобразования
// и тут как бы оптимизация вычислений
// но компилятор скорее всего и сам много чего оптимизирует
// и вынесет из циклов
// и об этом нужно помнить всегда
			col1 = float(img_in.cols - 1);
			row1 = float(img_in.rows - 1);
			col2 = col1 / 2;
			row2 = row1 / 2;

// это С++ часть. OpenCV делает теперь только так
// можно самому выделять очищать память,
// может и переделаю попозже
			Mat img_out(img_in.size(), img_in.type());
// поскольку всё преобразование делается через remap
// то тут хранятся вычисляемые параметры
			Mat map_r(img_in.size(), CV_32FC1);
			Mat map_c(img_in.size(), CV_32FC1);

			Mat map_r_s(img_in.size(), CV_32FC1);
			Mat map_c_s(img_in.size(), CV_32FC1);

			Mat map_r_ss(img_in.size(), CV_32FC1);
			Mat map_c_ss(img_in.size(), CV_32FC1);

			Mat map_r_sss(img_in.size(), CV_32FC1);
			Mat map_c_sss(img_in.size(), CV_32FC1);
// в массиве param хранятся параметры придуманного автором искажения картинок
// где то угол поворота, где то сжатие или растяжение по
// горизонтали или вертикали
//
			param[PERIOD_0] = 0.5 + 1.5 * (float) rand() / (float) (RAND_MAX);
			param[AMPLITUDE_0] = (0.125
					+ 0.125 * (float((rand() % 256) - 128) / 255.));
			param[SIGN_0] = rand_101();
			param[ANGLE_0] = 0.125 * M_PI;

			param[PERIOD_1] = 0.5 + 1.5 * (float) rand() / (float) (RAND_MAX);
			param[AMPLITUDE_1] = float(img_in.rows) / 10.;
			param[AMPLITUDE_1] = param[AMPLITUDE_1]
					* (1. + 0.5 * (0.5 - (float) rand() / (float) (RAND_MAX)));
			param[SIGN_1] = rand_101();
			param[ANGLE_1] = 0.125 * M_PI;

			param[PERIOD_2] = 0.5 + 1.5 * (float) rand() / (float) (RAND_MAX);
			param[AMPLITUDE_2] = float(img_in.cols) / 10.;
			param[AMPLITUDE_2] = param[AMPLITUDE_2]
					* (1. + 0.75 * (0.5 - (float) rand() / (float) (RAND_MAX)));
			param[SIGN_2] = rand_101();
			param[ANGLE_2] = 0.125 * M_PI;

// вот тут собственно и вычисляем map для remap
			for (i = 0; i < img_in.rows; i++) {
				f_i = float(i);
				row = f_i - row2;
				angle_i = param[PERIOD_1] * M_PI * f_i / row1;
				for (j = 0; j < img_in.cols; j++) {
					f_j = float(j);
					col = f_j - col2;

					tt = (1. + sin(-M_PI / 2 + 4. * M_PI * f_j / col1)) / 2;
					if (col > 0)
						tt = -tt;
					map_c_s.at<float>(i, j) = (f_j
							- tt * (col1 / 7) * 0.5
									* sin(param[SIGN_1] * angle_i));
					map_r_s.at<float>(i, j) = f_i;

					angle_j = param[PERIOD_2] * M_PI * f_j / col1;
					tt = (1. + sin(-M_PI / 2 + 4. * M_PI * f_i / row1)) / 2;
					if (row > 0)
						tt = -tt;
					map_c_ss.at<float>(i, j) = f_j;
					map_r_ss.at<float>(i, j) = (f_i
							- tt * (row1 / 7) * 0.5
									* sin(param[SIGN_2] * angle_j));

					tt = (1. - abs(col) / col2) * (1. - abs(row) / row2);
					angle_j = param[SIGN_0] * param[AMPLITUDE_0] * M_PI
							* sin(M_PI * tt);
					map_r.at<float>(i, j) = row * cos(angle_j)
							- col * sin(angle_j) + float(img_in.rows) / 2;
					map_c.at<float>(i, j) = row * sin(angle_j)
							+ col * cos(angle_j) + float(img_in.cols) / 2;
				}
			}

			img_in.copyTo(img_out);
// применяем эти ремапы по очереди
// один из них крутить, два других сжимают-растягивают
			remap(img_out, img_out, map_c_s, map_r_s, INTER_LINEAR,
					BORDER_CONSTANT, Scalar(0, 0, 0));
			remap(img_out, img_out, map_c_ss, map_r_ss, INTER_LINEAR,
					BORDER_CONSTANT, Scalar(0, 0, 0));
			remap(img_out, img_out, map_c, map_r, INTER_LINEAR, BORDER_CONSTANT,
					Scalar(0, 0, 0));

			bzero(out_file_path, PATH_MAX);
			sprintf(out_file_path, "%s%03d%s", "data/images/", thread_idx,
					file_name);

			try {
// всё, что получили пишем в рабочий файл
				imwrite(out_file_path, img_out);
			} catch (cv::Exception &e) {
				const char *err_msg = e.what();
				fprintf(log_file,
						" thread %d. write file exception caught: %s \n ",
						thread_idx, err_msg);
				fflush(log_file);
				error_idx = WRITE_FILE_EXEPTION;
				continue;
			}
// сохраняем время завершения обработки OpenCV
			s_time = time(NULL);
			localtime_r(&s_time, &m_time);
			sprintf(log_txt + strlen(log_txt), "\topencv   end time %s",
					asctime_r(&m_time, time_buf));

// формируем команду ОС для передачи файла по назначению
// адрес 10.0.1.1 это адрес VPN сервера при обращении через VPN
// по этому адресу наш FreeBSD сервер во внешнем мире
// и картинка поедет дважды шифрованная
// можно указать FRONT_ADDR и картинка будт отправлена на
// сервер во внешнем мире другим путём.
// на внешнем FreeBSD сервере можно порт SSH на FRONT_ADDR
// совсем закрыть и сервер будет доступен только через VPN
			bzero(exec_txt, BUFLEN_TXT);
			sprintf(exec_txt,
					"scp %s funhouse@10.0.1.1:/usr/local/www/data/images/%03d%.*s",
// 					"cp %s /var/www/html/images/%03d%.*s",
// для локального использования или тестирования используем cp
// если lighttpd запущен на этом же сервере, то можно и scp использовать
// и cp для примера
					out_file_path, thread_idx, (int) strlen(file_name),
					file_name);
// и отправляем файл через VPN на сервер в сети.
			if (system(exec_txt) != 0) {
				fprintf(log_file,
						" thread %d. File %s not moved successfully\n",
						thread_idx, out_file_path);
				error_idx = ERROR_TRANFER_RES_FILE;
				continue;
			}

			bzero(fcgi_txt, BUFLEN_TXT);
// начинает готовить HTML страницу
// готовим fcgi ответы в виде запросов
// в тексте которых имя файла, параметры,соль и хеш
// хеш конечно же можно проверить потом
			t_pointer = fcgi_txt;
			for (i = 0; i < PARAMETERS_NUM; i++) {
				memcpy(t_pointer, &param[i], sizeof(param[i]));
				t_pointer += sizeof(param[i]);
				sprintf(log_txt + strlen(log_txt), "\tparameter_%0d=%f\n", i,
						param[i]);
			}
			for (i = 0; i < SALT_LEN; i++) {
				salt = rand() % 256;
				memcpy(t_pointer, &salt, sizeof(salt));
				t_pointer += sizeof(salt);
			}
			memcpy(t_pointer, file_name, strlen(file_name));
			SHA256((const unsigned char*) fcgi_txt,
					(size_t) (PARAMETERS_NUM * sizeof(param[ANGLE_1])
							+ SALT_LEN * sizeof(salt) + strlen(file_name)),
					md_buf);
// fcgi запросы-ответы на наши вопросы, готовы и теперь строим HTML страницу
			bzero(html_txt, BUFLEN_TXT);
			sprintf(html_txt + strlen(html_txt), "Status: 200 OK\r\n");
			sprintf(html_txt + strlen(html_txt),
					"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01//EN\" \"http://www.w3.org/TR/html4/strict.dtd\">\r\n");
			sprintf(html_txt + strlen(html_txt),
					"Content-Type: text/html\r\n\r\n");
			sprintf(html_txt + strlen(html_txt),
					"<html>\r\n<meta charset=\"utf-8\">\r\n");
			sprintf(html_txt + strlen(html_txt), "<body>\r\n");
// если картинка большая для показа, то указываем браузеру размер для сжатия
			img_width =
					img_out.cols > MAX_IMAGE_ROWS ?
							MAX_IMAGE_ROWS : img_out.cols;
			sprintf(html_txt + strlen(html_txt),
					"  <img src=http://%s/images/%03d%s alt=\"Computed image\" style=\"width:%dpx\" >\r\n",
					FRONT_ADDR, thread_idx, file_name, img_width);
			sprintf(html_txt + strlen(html_txt), "<form>\n");
// здесь двоичный код с именем файла, параметрами, солью и хешем преобразовываем в код из букв
// кодировка base64 не годится,там есть непригодные для HTML символы
// кодировку base58 запустить не получилось
// то ли лень, то ли не сообразил как
			bzero(hex_txt, BUFLEN_TXT);
			char2hex(hex_txt, (char*) md_buf, SHA256_DIGEST_LENGTH);

			char2hex(hex_txt + 2 * SHA256_DIGEST_LENGTH, fcgi_txt,
					PARAMETERS_NUM * sizeof(param[ANGLE_1])
							+ SALT_LEN * sizeof(salt) + strlen(file_name));
// добавляем в страницу строки с опросами в ответе которых прошит FastCGI запрос
// с именем файла, параметрами, солью и хеш
			sprintf(html_txt + strlen(html_txt),
					"<p><button type=\"submit\" formaction=\"%*s.yes.fcgi\"> НРАВИТСЯ </button></p>\n",
					(int) strlen(hex_txt), hex_txt);
			sprintf(html_txt + strlen(html_txt),
					"<p><button type=\"submit\" formaction=\"%*s.no.fcgi\"> ОТКАЗАТЬ </button></p>\n",
					(int) strlen(hex_txt), hex_txt);
			sprintf(html_txt + strlen(html_txt),
					"<p><button type=\"submit\" formaction=\"upload.html\"> ЕЩЕ КАРТИНКУ </button></p>\n");
// если посетитель нажмет какую либо из кнопок
// то fcgi запрос придет на вход этой программы
			sprintf(html_txt + strlen(html_txt), "</form>");
			sprintf(html_txt + strlen(html_txt), "</body>\r\n</html>\r\n");

// тут только отправляем сформированную страницу ввнешний, FreeBSD, сервер
// в странице показ обработанной картинки и три ответа на вопрос "ДА" "НЕТ" "ОТЛОЖИТЬ"
			if ((ret = FCGX_PutS(html_txt, request.out)) < 0) {
				error_idx = ERROR_FASTCGI_SEND;
				continue;
			};

			sprintf(log_txt + strlen(log_txt), "\t%s\n", "send page");
			break;
		}
		if (error_idx != 0) {
// если во время парсинга или скачивания или еще когда
// возникла ошибка и мы это поняли,
// то вот тут формируется страница перехода на начальную страницу нашего сайта
			bzero(html_txt, BUFLEN_TXT);

			sprintf(html_txt + strlen(html_txt),
					"Status: 200 OK\r\nContent-Type: text/html\r\n\r\n");
			sprintf(html_txt + strlen(html_txt), "<head>\n");
			sprintf(html_txt + strlen(html_txt),
					"<meta http-equiv=\"refresh\" content=\"0;URL=http://%s/upload.html\"\n", FRONT_ADDR);
			sprintf(html_txt + strlen(html_txt), "</head>");
			printf("%s\n", html_txt);
			FCGX_PutS(html_txt, request.out);

			sprintf(log_txt + strlen(log_txt), "\t%s error %d\n",
					"Moved to upload page", error_idx);
			fflush(log_file);
			error_idx = 0;
		}

// все, что смогли или что получилось показали и нужно
//закрыть текущее соединение
		FCGX_Finish_r(&request);

//завершающие действия - запись статистики, логгирование ошибок и т.п.
		s_time = time(NULL);
		localtime_r(&s_time, &m_time);
		sprintf(log_txt + strlen(log_txt), "\tend request %s",
				asctime_r(&m_time, time_buf));
		sprintf(log_txt + strlen(log_txt),
				"\terror_idx %d\n\t +++ FCGX_fin\n\n", error_idx);

// так как журнал у нас один для всех потоков, то нельзя допустить,
// что бы потоки писали в него в произвольное время - каша получится
// поэтому и пишем в журнал монопольно для потока
		pthread_mutex_lock(&log_mutex);
		fprintf(log_file, "%s", log_txt);
		fflush(log_file);
		pthread_mutex_unlock(&log_mutex);
	}
// ну и если вдруг как то программа решила завершиться
// мьютексы нужно вернуть
	pthread_mutex_destroy(&accept_mutex);
	pthread_mutex_destroy(&log_mutex);
	return NULL;
}

int main(void) {
	int i;

	int thread_num[THREAD_COUNT];
	pthread_t id[THREAD_COUNT];

// Создание файла журнала и файла записи результатов
	if ((log_file = fopen("./log/fun_house_mirror.log", "a")) == NULL) {
		perror("log file open error ");
		return (44);
	}
	if ((marks_file = fopen("./data/marks/fun_house_mirror.marks", "a")) == NULL) {
		perror("marks file open error ");
		return (44);
	}

	pid_t pid = getpid();

// habr.com/ru/post/154187/
//инициализация библиотеки
	FCGX_Init();
	fprintf(log_file,
			"\n\n\nfun_house_mirror started \nLib is inited pid %d \n", pid);
	fflush(log_file);

//открываем новый сокет
	socketId = FCGX_OpenSocket(SOCKET_PATH, 20);
	if (socketId < 0) {
//ошибка при открытии сокета
		fprintf(log_file, " socketID < 0 and = %d ", socketId);
		fflush(log_file);
		return (11);
	}
	fprintf(log_file, "Socket is opened\n");
	fflush(log_file);

// создаём рабочие потоки
// номер потока хранится массиве
	for (i = 0; i < THREAD_COUNT; i++) {
		thread_num[i] = i;
		pthread_create(&(id[i]), NULL, do_thread, &(thread_num[i]));
	}

// ждем завершения рабочих потоков
// в данном варианте там бесконечный цикл
// и поток может завершиться только по ошибке
// ждем всех
	for (i = 0; i < THREAD_COUNT; i++) {
		pthread_join(id[i], NULL);
		fprintf(log_file, "Thread %lu is joined\n", id[i]);
		fflush(log_file);
	}
	return 0;
}

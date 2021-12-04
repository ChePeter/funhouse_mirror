# funhouse_mirror
Искусственный интеллект лицом

или 

веб морда для ваших поделок ( Пет проект )
https://habr.com/ru/users/chepeter/posts/

<a href="https://github.com/ChePeter/funhouse_mirror /a>

Если ваши успехи в освоении data science и других наук дошли до стадии, когда вам есть что показать, то самое время глянуть на эту статью. Эта статья совсем не про искусственный интеллект и про искусственный интеллект далее в статье больше ни слова. Эта статья описывает один из способов получить из сети картинку, обработать её и отдать обратно. Как можно дешевле, надежней, быстрей (это конечно фантастика) Можно и с AI, можно и без AI, главное то, что есть обработчик картинок и есть что показать !

Недостатки этой статьи - простовата до невозможности, нет ни одного решения сложней плинтуса. Откровенный примитив. Всё уже описано, расписано и показано в других статьях.

Достоинства этой статьи - применены исключительно простые решения. Все конфиги на пол страницы, все библиотеки многолетней давности и никаких фреймворков. Всё ясно, понятно, обозримо и проверено годами. И работает.

Таких статей, как прикрутить web интерфейс к питону в десяток строк, полно, но дьявол то как всегда в мелочах. Если сделать вебморду в 10 строк, работать то оно конечно будет, но вам тогда нужен прямой IP и все боты мира будут в него стучать, отнимать ваше и время процессора. А если вдруг ушлый какой и пролезет! Не годится! Нужно защищать свой компьютер и, особенно, свой код, например нейронной выстраданной сети. Код, свой, еще не опубликованный и незакопирайченый здесь главная ценность.

Поэтому выносим морду в интернет, защищаем её и строим к ней туннель. 

Покупаем/арендуем/берем_в_дар  VDS, самый махонький. Я выбрал вариант KVM, чтобы спокойно и уверенно установить там FreeBSD. Их как-то в сети внешней  работает много и все сетевые трюки на FreeBSD выглядят просто, достойно и элегантно. ( и всё это дело можно уместить в 512, а то и в 128 Мб памяти, что немаловажно по деньгам)

Туннелей тоже много разных и хороших, мой выбор - OpenVPN. Бесплатно и просто подключить свой внутренний вычисляющий сервер на любой ОС к внешнему серверу на FreeBSD.

Вот тут первый вопрос — а где делать сервер и где клиент? Я выбрал вариант когда во внешнем мире на VDS у меня находится сервер. Казалось бы должно быть наоборот, сервер внутри охраняемого периметра, а клиент вне и клиент подключается к серверу. Но, в моем случае, если потерять внешний сервер, если сервер будет скомпрометирован, то я потеряю всего лишь VDS и не потеряю доступ внутрь, к суперсекретному своему алгоритму и к машине, на которой он есть, в охраняемом периметре. Если же вне будет клиент, а сервер внутри, то при компрометации клиента или взломе его, утекут ключи и хакер получит доступ с серверу с секретным кодом. В варианте внешнего сервера нет никаких открытых и пробрасываемых портов, все наглухо закрыто для доступа извне, доступ только через VPN и только по одному порту для FastCGI.

Итак ставим на VSD с FreeBSD обычный web сервер lighttpd, обычный OpenVPN сервер и посредством FastCGI отправляем картинки через openvpn на свой рабочий компьютер для обработки.

Первый архитектурный вопрос прояснился и буду рад и готов получить замечания и предложения.

Но теперь второй вопрос.  Картинку то мы получили, обработку, которую собственно и хотим показать миру, сделали и теперь картинку нужно отдать обратно в мир. Но вот вопрос: - а с какого сервера? Если из своего рабочего, то те же проблемы - прямой IP и соблазн для ботов всего мира. Если не прямой, то нужно с сервера обработки отдать картинку куда то во внешний мир безопасно и оттуда показывать. В данном варианте картинка грузится через VPN с помощью scp обратно на внешний сервер на FreeBSD и оттуда отдается тем же lighttpd. Картинку покажем и через 10 минут удалим, так что во внешнем мире не хранится ничего, ни картинки, ни алгоритм.

Отдав картинку, lighhtpd показывает страницу опроса с закодированными параметрами картинки - нравится преобразованная картинка или нет или загрузить новую? Ответ вместе с параметрами преобразования картинки  и ее именем возвращается по FastCGI на внутренний сервер и записывается в файл. Мало ли, вдруг накопится статистика )) Сделано так, что бы у пользователя было время подумать, отвлекли, пообедать ушел и т.д. Сессия разорвалась и что бы ответить нужна новая, вот в новом FastCGI запросе и будет новая сессия и вся инфо о картинке будет отправлена.

Ну и опять же конечно буду рад и готов получить замечания и предложения.

Вот такая идея и действующий макет есть по адресу http://107.189.8.250/

Теперь по пунктам и подробно. Еще раз - буду рад и готов выслушать замечания, правки и критику.


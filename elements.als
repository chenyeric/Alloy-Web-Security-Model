open network

abstract sig RequestAPI {
	owner: HTTPServer,
	method: Method,
	target: HTTPServer
} 

sig formElement extends RequestAPI {
}{
	method in GET+POST
}

sig XMLHTTPRequest extends RequestAPI {
	headers: set HTTPRequestHeader
}{
	target=owner
	no headers & (      AcceptCharset +
                                AcceptEncoding +
                                Connection +
                                ContentLength_Req +
                                Cookie +
//                                ContentTransferEncoding +
                                Date_Req +
                                Expect +
                                Host +
//                                KeepAlive +
                                Referer +
                                TE +
//                                Trailer +
//                                TransferEncoding +
                                Upgrade +
                                UserAgent +
                                Via_Req
						)

}

sig XMLHTTPRequest2 extends RequestAPI {
	headers: set HTTPHeader
}{
	target != owner implies method in GET+POST
}

	

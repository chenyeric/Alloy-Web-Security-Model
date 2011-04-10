open util/ordering[Time]
sig Time {}

abstract sig NetworkEndpoint{
}

//not really sure if we need a separate event class
abstract sig Event {
	pre,post : Time,

}



abstract sig NetworkEvent extends Event {
	from: NetworkEndpoint,
	to: NetworkEndpoint
}


abstract sig HTTPServer extends NetworkEndpoint{	}

abstract sig HTTPClient extends NetworkEndpoint {}
abstract sig Browser extends HTTPClient {
}

abstract sig InternetExplorer,Firefox,Safari extends Browser { }


abstract sig Method{ }
one sig GET,POST,PUT,DELETE extends Method {}

sig ScriptContext { 
	owner : HTTPServer,
	location : Browser
}


sig HTTPRequest extends NetworkEvent {
    method: Method,
	scriptContext : ScriptContext
	//no URL line for now
}{
	from in HTTPClient
	to in HTTPServer
	from in Browser implies scriptContext.location = from
}




abstract sig HTTPHeader {}
abstract sig HTTPResponseHeader extends HTTPHeader{} 
abstract sig HTTPRequestHeader extends HTTPHeader{}
abstract sig Status  {}
one sig c200 extends Status{}
abstract sig RedirectionStatus extends Status {}

one sig c301,c302,c303,c304,c305,c306,c307 extends RedirectionStatus {}



sig location extends HTTPResponseHeader {
	target : lone HTTPServer 
}

sig HTTPResponse extends NetworkEvent {
		statusCode : Status ,
		headers : set HTTPResponseHeader

}{
	from in HTTPServer
	to in HTTPClient
	lone headers & location
//Maybe following should go into httpFacts
	let locationHeader = location & headers |
		statusCode in RedirectionStatus implies # locationHeader.target	= 1
}


sig HTTPTransaction {
	req : HTTPRequest,
	resp : HTTPResponse
}{
	req.from=resp.to
	resp.from=req.to
	resp.pre in req.post.*next
}


///////////////////////////////////////////////////////////////
// Maybe remove the common HTTPHeader Class and have only 2 disjoint classes

///

sig Accept extends HTTPRequestHeader{}
sig AcceptCharset extends HTTPRequestHeader{}
sig AcceptEncoding extends HTTPRequestHeader{}
sig AcceptLanguage extends HTTPRequestHeader{}
sig AcceptRanges extends HTTPRequestHeader{}
sig Authorization extends HTTPRequestHeader{}
sig CacheControl_Req extends HTTPRequestHeader{}
sig Connection extends HTTPRequestHeader{}
sig Cookie extends HTTPRequestHeader{}
sig ContentLength_Req extends HTTPRequestHeader{}
sig ContentType_Req extends HTTPRequestHeader{}
sig Date_Req extends HTTPRequestHeader{}
sig Expect extends HTTPRequestHeader{}
sig From extends HTTPRequestHeader{}
sig Host extends HTTPRequestHeader{}
sig IfMatch extends HTTPRequestHeader{}
sig IfModifiedSince extends HTTPRequestHeader{}
sig IfNoneMatch extends HTTPRequestHeader{}
sig IfRange extends HTTPRequestHeader{}
sig IfUnmodifiedSince extends HTTPRequestHeader{}
sig MaxForwards extends HTTPRequestHeader{}
sig Pragma_Req extends HTTPRequestHeader{}
sig ProxyAuthorization extends HTTPRequestHeader{}
sig Range extends HTTPRequestHeader{}
sig Referer extends HTTPRequestHeader{}
sig TE extends HTTPRequestHeader{}
sig Upgrade extends HTTPRequestHeader{}
sig UserAgent extends HTTPRequestHeader{}
sig Via_Req extends HTTPRequestHeader{}
sig Warn extends HTTPRequestHeader{}



sig Age extends HTTPResponseHeader{}
sig Allow extends HTTPResponseHeader{}
sig CacheControl_Resp extends HTTPResponseHeader{}
sig ContentEncoding extends HTTPResponseHeader{}
sig ContentLanguage extends HTTPResponseHeader{}
sig ContentLength_Resp extends HTTPResponseHeader{}
sig ContentLocation extends HTTPResponseHeader{}
sig ContentDisposition extends HTTPResponseHeader{}
sig ContentMD5 extends HTTPResponseHeader{}
sig ContentRange extends HTTPResponseHeader{}
sig ContentType_Resp extends HTTPResponseHeader{}
sig Date_Resp extends HTTPResponseHeader{}
sig ETag extends HTTPResponseHeader{}
sig Expires extends HTTPResponseHeader{}
sig LastModified extends HTTPResponseHeader{}
sig Pragma_Resp extends HTTPResponseHeader{}
sig ProxyAuthenticate extends HTTPResponseHeader{}
sig RetryAfter extends HTTPResponseHeader{}
sig Server extends HTTPResponseHeader{}
sig SetCookie extends HTTPResponseHeader{}
sig Trailer extends HTTPResponseHeader{}
sig TransferEncoding extends HTTPResponseHeader{}
sig Vary extends HTTPResponseHeader{}
sig Via_Resp extends HTTPResponseHeader{}
sig Warning extends HTTPResponseHeader{}
sig WWWAuthenticate extends HTTPResponseHeader{}


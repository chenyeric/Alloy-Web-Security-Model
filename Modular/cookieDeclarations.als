//open basicDeclarations
open cookieSigs


/* Enforce a common semantic between the
    to, from, and host of HTTP Requests and HTTP Responses */




/****************************
Cookie Stuff
****************************/


abstract sig Token {}

sig Cookie extends Secret {
	name : Token,
	value : Token,
	domain : DNS,
	path : Path,
 }{}

sig SecureCookie extends Cookie {}

sig CookieHeader extends HTTPRequestHeader{ thecookie : Cookie }
sig SetCookieHeader extends HTTPResponseHeader{	thecookie : Cookie }

fact SecureCookiesOnlySentOverHTTPS{
		all e:HTTPEvent,c:SecureCookie | {
				e.from in Browser + NormalPrincipal.servers
				httpPacketHasCookie[c,e]
		} implies e.host.schema=HTTPS

}


fact CookiesAreSameOriginAndSomeOneToldThemToTheClient{
	all areq:HTTPRequest |{ 
			areq.from in Browser  
			some ( areq.headers & CookieHeader)
	} implies  all acookie :(areq.headers & CookieHeader).thecookie | some aresp: location.(areq.from).transactions.resp | {
				//don't do same origin check as http cookies can go over https
				//isSubdomainOf[aresp.host.dnslabel, areq.host.dnslabel]
				acookie in (aresp.headers & SetCookieHeader).thecookie
                isSubdomainOf[aresp.host.dnslabel, acookie.domain] //JHB changed 5/16/11
                isSubdomainOf[areq.host.dnslabel, acookie.domain]
				happensBeforeOrdering[aresp,areq]
	}
}

pred httpPacketHasCookie[c:Cookie,httpevent:HTTPRequest+HTTPResponse]{
				(httpevent in HTTPRequest and  c in (httpevent.headers & CookieHeader).thecookie ) or
				(httpevent in HTTPResponse and c in (httpevent.headers & SetCookieHeader).thecookie)
}

pred hasKnowledgeViaUnencryptedHTTPEvent[c: Cookie, ne : NetworkEndpoint, usageEvent: Event]{ 
		ne !in WebPrincipal.servers + Browser //Question: should there be a line that relates ne to httpevent?
		some httpevent : HTTPEvent | {
			happensBeforeOrdering[httpevent,usageEvent]
			httpevent.host.schema = HTTP
			httpPacketHasCookie[c,httpevent]
		}
}

pred hasKnowledgeViaDirectHTTP[c:Cookie,ne:NetworkEndpoint,usageEvent:Event]{
		some t: HTTPTransaction | {
		happensBeforeOrdering[t.req,usageEvent]
		httpPacketHasCookie[c,t.req]
		t.resp.from = ne
	} or {
		happensBeforeOrdering[t.resp,usageEvent]
		httpPacketHasCookie[c,t.resp]
		some ((transactions.t).location & ne)
		}
}

pred hasKnowledgeCookie[c:Cookie,ne:NetworkEndpoint,usageEvent:Event]{
	ne in c.madeBy.servers or hasKnowledgeViaUnencryptedHTTPEvent[c,ne,usageEvent] or hasKnowledgeViaDirectHTTP[c,ne,usageEvent]
}

fact BeforeUsingCookieYouNeedToKnowAboutIt{
	all e:HTTPRequest + HTTPResponse | 
// Use httpPacketHasCookie
			all c:(e.(HTTPRequest <: headers) & CookieHeader).thecookie + (e.(HTTPResponse <: headers) & SetCookieHeader).thecookie |
					hasKnowledgeCookie[c,e.from,e]
}

fact NormalPrincipalsAndWebAttackersMakeCookiesWithTheirDomain{
	all e:HTTPResponse |
		all c:(e.headers & SetCookieHeader).thecookie | {
			e.from in (NormalPrincipal+WEBATTACKER).servers implies 
                 c.madeBy = e.from[servers] &&
                 some dns: e.host.dnslabel |   isSubdomainOf[dns,c.domain]//JHB 5-16-11
		}
}

fact NormalPrincipalsDontReuseCookies{
	all p:NormalPrincipal | no disj e1,e2:HTTPResponse | {
			(e1.from + e2.from) in p.servers 
			some ( 	(e1.headers & SetCookieHeader).thecookie & (e2.headers & SetCookieHeader).thecookie )
	}
}

open httpFacts

fact FirefoxRedirection {
	all first,second:HTTPTransaction | 
			first->second in Globals.redirectResponse and first.req.from in Firefox 
				implies {
					first.resp.statusCode in c301+c302+c303+c304+c307
					first.resp.statusCode in c301+c302+c303 implies second.req.method=GET
					first.resp.statusCode in c304 implies first.req.method=GET
					first.resp.statusCode in c304+c307 implies second.req.method=first.req.method
			}
}
					
fact SafariRedirection{
	all first,second:HTTPTransaction | 
			first->second in Globals.redirectResponse and first.req.from in Safari 
				implies {
					first.resp.statusCode in c301+c302+c303+c305+c306+c307
					second.req.method=GET
			}
}



fact IERedirection {
	all first,second:HTTPTransaction | 
			first->second in Globals.redirectResponse and first.req.from in InternetExplorer
				implies {
					first.resp.statusCode in c301+c302+c303+c307
					first.req.method in PUT+DELETE or first.resp.statusCode=c307 implies second.req.method=first.req.method
					first.resp.statusCode in c302+c303 and first.req.method = POST implies second.req.method=GET
					first.resp.statusCode in c301 and first.req.method in POST+GET implies second.req.method=GET
					first.req.method=GET implies first.resp.statusCode in c301
			}
}
			


//all redirects actually cause it to be in redirectResponse
fact redirectResponseIsComplete{ 
	all first:HTTPTransaction | 
		first.resp.statusCode in RedirectionStatus implies 
			some second:HTTPTransaction | first->second in Globals.redirectResponse
}

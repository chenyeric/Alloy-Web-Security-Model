open network
open elements

one sig Globals {
	//equivalent to saying all b:HTTPTransactions | lone redirectPairs.b
	// that is for all HTTPTransactions, there is atmost one Transaction
	//which is its parent
	redirectResponse : HTTPTransaction lone -> HTTPTransaction,
// Is this really a one to one relation ?
	causalAPI : HTTPRequest -> RequestAPI
}{
	all first,second:HTTPTransaction | first->second in redirectResponse implies {
			first.resp.statusCode in RedirectionStatus // do we really need this here? aren't we writing it in the browserBehaviour
			second.req.from = first.req.from
			second.req.scriptContext = first.req.scriptContext
			second.req.pre in first.resp.post.*next
			let l=first.resp.headers & location |
				second.req.to = l.target
		}

	all req:HTTPRequest - redirectResponse[HTTPTransaction].req | 
			some e:RequestAPI | req->e in causalAPI

	all req:HTTPRequest- redirectResponse[HTTPTransaction].req , e:RequestAPI | req->e in causalAPI implies {
				req.method=e.method
				req.to=e.target
				req.scriptContext.owner=e.owner
	}
}
		
fact noMagicResponse{
	HTTPResponse in HTTPTransaction.resp
	HTTPRequest in HTTPTransaction.req
}

fact uniqueTransactions {
	all disj t,t':HTTPTransaction | no (t.resp & t'.resp )
									and no (t.req & t'.req)
}

fact XHRNoCrossOrigin{
	all t,t':HTTPTransaction | 
		t.req.to != t'.req.to and t->t' in Globals.redirectResponse 
			 implies no 	Globals.causalAPI[t.req] & (XMLHTTPRequest + XMLHTTPRequest2)
			
}

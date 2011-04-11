open declarations
open browserFacts
open requestAPIFacts
/*****************************************************
**                                                                            **
**                           Strict Entry                                **
**                                                                            **
*****************************************************/

/* New Declarations */

//server
sig StrictEntryOrigin extends Origin {}
{
  //StrictEntryOrigins only include good guys, no attackers
  //do it this way (doesn't consider DNS rebinding (web level attacker)
   getPrincipalFromOrigin[StrictEntryOrigin] in NormalPrincipal
}

pred isRequestToStrictEntryOrigin[request:HTTPRequest]{
	request.host in StrictEntryOrigin
}

//browser
sig StrictEntryBrowser extends Firefox3{}  //just a random choice, to get some redirect behavior

//fact about strict entry of browser
/* We reuse SENSITIVE as path that is not strict entry, and PUBLIC as the entry point */

//A scriptcontext running on a browser that is strict-entry compliant will never make 
//Cross origin HTTP requests for SENSTIVE path to non-entry points origins

//Previous version that is vulnerable to redirect attack
//fact StrictEntryEnforcement {
//       all sc:ScriptContext | sc.location=StrictEntryBrowser implies 
//           no requ:sc.transactions.req | { 
//                  requ.path=SENSITIVE
//                  ( isCrossOriginRequest[requ] and isRequestToStrictEntryOrigin[requ])
//                 }
//}

//fixed version
fact StrictEntryEnforcement {
       all sc:ScriptContext | sc.location=StrictEntryBrowser implies 
           no requ:sc.transactions.req | { 
                  requ.path=SENSITIVE
                  not (lone involvedOrigins[req.requ])
                  isRequestToStrictEntryOrigin[requ]
           }
}


run show {} for 6

run SESameOriginSensitiveOK {
     some sc:ScriptContext | sc.location=StrictEntryBrowser && {
         some requ:HTTPRequest | {
         requ in sc.transactions.req
         isRequestToStrictEntryOrigin[requ]
         !isCrossOriginRequest[requ]
         requ.path = SENSITIVE 
         }
     }
}  for 8 but exactly 1 SENSITIVE, exactly 1 StrictEntryBrowser

run SECrossOriginPublicOK {
     some sc:ScriptContext | sc.location=StrictEntryBrowser && {
         some requ:HTTPRequest | {
         requ in sc.transactions.req
         isRequestToStrictEntryOrigin[requ]
         isCrossOriginRequest[requ]
         requ.path = PUBLIC 
         }
     }
}  for 8 but exactly 1 PUBLIC, exactly 1 StrictEntryBrowser

run NonSECrossOriginSensOK {
     some sc:ScriptContext | sc.location=StrictEntryBrowser && {
         some requ:HTTPRequest | {
         requ in sc.transactions.req
         !isRequestToStrictEntryOrigin[requ]
         isCrossOriginRequest[requ]
         requ.path = SENSITIVE 
         }
     }
}  for 6 but exactly 1 SENSITIVE, exactly 1 StrictEntryBrowser



//sanity check

run redirectsHappen {
   some t:ScriptContext.transactions {
       t.cause in HTTPTransaction  
   } 
}
for 8 but 1 c301


//run redirectsAcrossDomainHappen {
//      some t:HTTPTransaction | 
//         some (involvedServers[t] & (Principal.servers - getPrincipalFromOrigin[t.req.host].servers))
//} for 6

// do we want to define some server behavior w.r.t. redirects?

check strictEntryProtectsFromSensitiveAccess{

	no t:HTTPTransaction | {
		// Transaction is in a StrictEntry Browser
		some( (transactions.t).location & (StrictEntryBrowser))
		//Intended for an StrictEntry Origin
        some( t.req.host & StrictEntryOrigin)
		// Its a non trivial request
		t.req.method in Method - safeMethods
        // For a sensitive path
        t.req.path = SENSITIVE
		// The Right Principal Responds
		some t.resp
		t.resp.from in getPrincipalFromOrigin[StrictEntryOrigin].servers
        //only c200 responses
		t.resp.statusCode = c200

		//And the WebAttacker is somehow involved in the causal chain
		some (WEBATTACKER.servers &	 involvedServers[t])
	}

} for 8 but 0 ACTIVEATTACKER, 1 WEBATTACKER, exactly 1 StrictEntryBrowser, exactly 1 StrictEntryOrigin, 1 SENSITIVE // 0 ORIGINAWARE, 0 GOOD, 0 SECURE ,0 Secret, //1 HTTPClient//, 2 Origin, 0 PreFlightRequest, 0 CORSRequestHeader, 0 CORSResponseHeader, 0 Secret//,8 Time//, 1 RequestAPI, 0 Secret
//The above assertion failed with the same attack scenario as for CSRF
//Link between one strict origin site and an attacker site, redirected back to strict origin site

fact {
	NetworkEndpoint = Principal.servers + HTTPClient
//	all sc:ScriptContext | no disj t1,t2:sc.transactions | some ( t1.cause & t2.cause & HTTPTransaction)
//	no client:HTTPClient | client in Principal.servers
//	all t1,t2:HTTPTransaction | t1=t2.cause implies t1+t2 in ScriptContext.transactions

	// ScriptContext only connects to DNSLabels that it knows exists/owned by some Principal
	DNS in Principal.dnslabels
}

fun involvedServers[t:HTTPTransaction]:set NetworkEndpoint{
( (t.*cause & HTTPTransaction).resp.from + getPrincipalFromOrigin[(transactions.t).owner].servers )
}

fun involvedOrigins[t:HTTPTransaction]:set Origin{
  (t.*cause & HTTPTransaction).resp.host + (transactions.t).owner
}

//want to run some sort of test to say that no attacker principle can be involved or something

//questions: actual implementation (what's the tests)
//HTTP/HTTPS?


  

open declarations_cookie_update as d

//Isolated Cookies are now bound to additional param, a specific RenderingEngine.
sig IsoCookie extends SecureCookie  { binding: one RenderingEngine }


//BrowserImplementing cookieIso
sig cookieIsoBrowser extends Browser{ } 


fact BrowserKernelCorrectlyTagsReceivedIsoCookies{
    all p:RenderingEngine |
     some ((p.contexts.transactions.resp.headers & SetCookieHeader).thecookie.binding) implies
       (p.contexts.transactions.resp.headers & SetCookieHeader).thecookie.binding = p
}

fact IsoCookiesSentOnlyByAppropriateEngine {
    no p:RenderingEngine | 
        some cookies:((p.contexts.transactions.req.headers & CookieHeader).thecookie & IsoCookie) |
                  cookies.binding != p 
}

fact IsoCookiesSentOnlyToDomain {
    no areq:ScriptContext.transactions.req |
       some cookies:((areq.headers & CookieHeader).thecookie & IsoCookie) | 
             cookies.domain != areq.host.dnslabel
}

//fact allMatchingCookieHeadersSent {
//    all d:DNS, areq:isoContext.transactions.req | 
//      areq.host.dnslabel = d implies
//         (areq.headers & CookieHeader)  = ((thecookie.domain.d) <: CookieHeader)
//}



//Contexts for app versus not, in browsers implementing cookie isolation
//Trying to capture notion of what caused the app context.  A user, or another ScriptContext opening
//a new browser window/tab
sig isoContext extends ScriptContext{
   cause: one (ScriptContext)+User,
   initialURL: one URL             
} 
{location = cookieIsoBrowser}


fact initalURLCausesTransaction {
    all iso:isoContext, i:iso.initialURL |
         some areq:HTTPRequest | {
            areq.host = i.host
            areq.path = i.path
            areq in iso.transactions.req
         }
}

sig isoContextFixed extends isoContext {}{}
//Need some fact about one context can only cause another if the initialURL if new one is an app
//and new URL is in app

fact causesOfNewIsoContext {
   all iso1:isoContext, iso2: isoContextFixed | 
		(iso2.cause = iso1) =>  //Reasons iso1 be the cause of iso2
			(iso2.initialURL.path = ENTRY_POINT) || //The initial URL is an entry point
			(iso1.owner = iso2.owner and iso1.engine = iso2.engine) //The two contexts are "Same-Origin"
}




run AppContextCausedByAttacker {
   some iso:isoContext | {
      some (iso.cause & ScriptContext)
      getPrincipalFromOrigin[iso.cause.owner] in WEBATTACKER
      iso.initialURL.path = PATH_TO_COMPROMISE
   }
} for 6 


sig CredentialCookie extends SecureCookie{}



run subResourceCSRFPossible {
  some attackContext:isoContext | {
     some p:attackContext.owner.dnslabel.(~dnslabels) | p  in WEBATTACKER
     some areq:attackContext.transactions.req | {
         some q:areq.host.dnslabel.(~dnslabels) |
              { q in NormalPrincipal
                //Credentials were not directly issued by this NormalPrincipal to this context
                //Commenting this no quantifier out makes the check fail
                no hdr:(attackContext.transactions.resp.headers & SetCookieHeader) |   
                     hdr.thecookie in IsoCookie && hdr.thecookie.domain in q.dnslabels
              }
         areq.path = PATH_TO_COMPROMISE
         some hdrs:(areq.headers & CookieHeader) | {
                  hdrs.thecookie in CredentialCookie 
         }
     }
  }
}
for 6


run goodRequestPossible{
  some c:ScriptContext, areq: c.transactions.req, o:c.owner | {
        o = areq.host
        o.dnslabel.(~dnslabels) in NormalPrincipal
        areq.path = PATH_TO_COMPROMISE
        some hdrs:(areq.headers & CookieHeader) | {
                  hdrs.thecookie in IsoCookie 
        }
  }
} for 6



check isoSubResourceCSRFNotPossible {
  no attackContext:isoContext | {
     some p:attackContext.owner.dnslabel.(~dnslabels) | p  in WEBATTACKER
     some areq:attackContext.transactions.req | {
         some q:areq.host.dnslabel.(~dnslabels) |
              { q in NormalPrincipal
                //Credentials were not directly issued by this NormalPrincipal to any context in the same RenderingEngine
                //Commenting this no quantifier out makes the check fail
                no hdr:(attackContext.engine.contexts.transactions.resp.headers & SetCookieHeader) |   
                     hdr.thecookie in IsoCookie && hdr.thecookie.domain in q.dnslabels
              }
         areq.path = PATH_TO_COMPROMISE
         some hdrs:(areq.headers & CookieHeader) | {
                  hdrs.thecookie in IsoCookie 
         }
     }
  }
}
for 6

//No attackcontext is able to cause another context in another renderingEngine 
//containing a packet with an isocookie
//to a normal principal for a PATH_TO_COMPROMISE

check noAttackByCausingAnotherContext {
  no disj atkC, victC : isoContext | {
      some p:atkC.owner.dnslabel.(~dnslabels) | p in WEBATTACKER
      victC.cause = atkC
      //they're in different engines
      victC.engine != atkC.engine
      some areq:victC.transactions.req | {
          some q:areq.host.dnslabel.(~dnslabels) | 
                {q in NormalPrincipal
                 //There is no legitimate login after the victim context is spawned
                 no hdr:(victC.transactions.resp.headers & SetCookieHeader) |   
                      hdr.thecookie in IsoCookie && hdr.thecookie.domain in q.dnslabels
                }             
          areq.path = PATH_TO_COMPROMISE
          some hdrs:(areq.headers & CookieHeader) | hdrs.thecookie in IsoCookie
     }
  }
}
for 6

//The fixed version of above, considering RenderingEngines
check noAttackByCausingAnotherContextFixed {
  no atkC:isoContext, victC : isoContextFixed | {
      some p:atkC.owner.dnslabel.(~dnslabels) | p in WEBATTACKER
      victC.cause = atkC
      //they're in different engines
      victC.engine != atkC.engine
      some areq:victC.transactions.req | {
          some q:areq.host.dnslabel.(~dnslabels) | 
                {q in NormalPrincipal
                 //There is no legitimate login after the victim context is spawned
                 no hdr:(victC.transactions.resp.headers & SetCookieHeader) |   
                      hdr.thecookie in IsoCookie && hdr.thecookie.domain in q.dnslabels
                }             
          areq.path = PATH_TO_COMPROMISE
          some hdrs:(areq.headers & CookieHeader) | hdrs.thecookie in IsoCookie
     }
  }
}
for 6

//Design some arbitrary credentials


//************ NEED NOTION OF 
// non app context can open a new window in an app context

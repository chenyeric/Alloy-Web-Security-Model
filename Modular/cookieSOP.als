open basicDeclarations as d
open cookieDeclarations as c

/* The cookie Same-Origin Policy 
Goal #1: Describe the related origin attacker */


fact cookiesSentOnlyToDomain {
    no areq:ScriptContext.transactions.req | {
       (transactions.req.areq).location in Browser
       some cookies:((areq.headers & CookieHeader).thecookie) | 
             !isSubdomainOf[areq.host.dnslabel, cookies.domain]
   }
}

run subdomains {
   some d1, d2: DNS  | {
         d1.(~dnslabels) in WEBATTACKER
         d2.(~dnslabels) in NormalPrincipal
         isSubdomainOf[d1,d2]
   }
} for 1

run relatedSubdomainSetting  {
   some t:HTTPTransaction, c:(t.req.headers & CookieHeader).thecookie | {
        some (transactions.t).location
	    (transactions.t).location in Browser
        some t.req.host.dnslabel.(~dnslabels)
        t.req.host.dnslabel.(~dnslabels) in NormalPrincipal
        t.req.host.dnslabel != c.domain
        c.madeBy = WEBATTACKER
   }   
} for 4 but 0 ACTIVEATTACKER, 0 PASSIVEATTACKER


/*
run maliciousCookieSetting {
   some c:Cookie | {
        some c.madeBy
        c.madeBy in WEBATTACKER
        some c.domain.(~dnslabels)
        c.domain.(~dnslabels) in NormalPrincipal
   }
} for 2 but  0 ACTIVEATTACKER, 0 PASSIVEATTACKER
*/

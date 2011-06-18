open util/boolean as b
open DNSAndOrigin 

abstract sig Token {}

sig Cookie {  //extends Secret {
    setBy : one Origin,
	name : Token,
	value : Token,
	domain : lone DNS, // this is according to the wildcard behavior of cookies.  Only if this field is empty, the scope is then
                                 // is limited to DNS name in the setBy Origin 
	path : Path,
    secure : Bool,
    httponly : Bool
} {
    some domain => { isSubdomainOf[setBy.@dnslabel, domain]  //the domain label can only be "shortened"
                                 domain.parent != DNSRoot }
}



pred DomainInCookieScope [d:DNS, c:Cookie] {
    (no c.domain and d=c.setBy.dnslabel)  or //no wildcards when domain is not set.  exact match only
    (some c.domain and isSubdomainOf[d, c.domain]) // isSubdomainOf is inclusive
}


pred isSecureCookie[c:Cookie] { isTrue[c.secure] }
pred isHttponlyCookie [c:Cookie] { isTrue[c.httponly] }

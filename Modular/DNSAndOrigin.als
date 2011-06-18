sig DNS{
	parent : DNS + DNSRoot,
	resolvesTo : set NetworkEndpoint
}{
// A DNS Label resolvesTo something
	some resolvesTo
}

one sig DNSRoot {}

fact dnsIsAcyclic {
	 all x: DNS | x !in x.^parent
//	 all x:dns-dnsRoot | some x.parent
}

// s is  a subdomain of d
pred isSubdomainOf[s: DNS, d: DNS]{
  // e.g. .stanford.edu is a subdomain of .edu
  d in s.*parent
}

pred isSiblingDomainOf[s1:DNS, s2:DNS] {
  s1 != s2
  s1.parent = s2.parent
}

//a sig for DNS wildcards where only * is only allowed, only in the left-most, or more specific, position
//Semantically, a DNSWildCard without a suffix is '*'.
sig DNSWildCard{ 
    suffix : lone DNS   // the portion after the *.    
}

//tests to see if w1 encompasses all of w2.
//For example, when w1 = *.mit.edu and w2=*.login.mit.edu
pred DNSWildCardEncompasses[w1:DNSWildCard, w2:DNSWildCard] {
   ( no w1.suffix) or //w1 is *
   {    some w1.suffix  //w1 is not * 
        some w2.suffix  //w2 is not *
        isSubdomainOf[w2.suffix, w1.suffix]
   }
}

//The classic (non-cookie) definition of wildcard matching
//So, a.example.com matches *.example.com, but example.com does not match *.example.com
pred matchesDNSWildcard [d:DNS, w:DNSWildCard] {
  (no w.suffix) or // w is *
  {   some w.suffix // w is not *
      isSubdomainOf[d.parent,w.suffix]
  }
}

run {
  some d:DNSWildCard | no d.suffix}
for 2

sig NetworkEndpoint{}




sig Origin {
//	port: Port, 
	schema: Schema,
	dnslabel : DNS,
}

fact DistinctOrigins {
  no disj o1, o2: Origin | {
     //o1.port = o2.port
     o1.schema = o2.schema
     o1.dnslabel = o2.dnslabel
  }
}

//enum Port{P80,P8080}
enum Schema{HTTP,HTTPS, DATA}

abstract sig Path{}
sig INDEX,HOME,SENSITIVE, PUBLIC, LOGIN,LOGOUT,REDIRECT, ENTRY_POINT extends Path{}
sig PATH_TO_COMPROMISE extends SENSITIVE {}


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
  s1.parent = s2.parent
}

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
enum Schema{HTTP,HTTPS}

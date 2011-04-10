open declarations
open browserFacts
//open httpFacts
open requestAPIFacts

// open safariFacts
// open firefoxFacts
// open IEFacts
open serverFacts

/*
   Solver=sat4j Bitwidth=4 MaxSeq=5 SkolemDepth=1 Symmetry=20
   104489 vars. 1666 primary vars. 218486 clauses. 119290ms.
   Instance found. Predicate is consistent. 794ms.
*/
run show {} for 5

/*
  104683 vars. 1671 primary vars. 219084 clauses. 121333ms.
   Solving...
   End solveAll()
   Instance found. Predicate is consistent. 1673ms.
*/
run SameOriginRedirectsPossible{
	some t:HTTPTransaction |{
		t.cause in HTTPTransaction
		t.req.host = t.cause.req.host
	}
} for 5



// For 8, Instance found. Predicate is consistent. 86948ms.
// For 7, Instance found. Predicate is consistent. 28246ms.
// For 6, no instance found. Predicate may be inconsistent. 6066ms.
run XHR2SimpleToComplexRedirect{
some t,t':HTTPTransaction | t.cause=t' and complexCORSTransaction[t] and t.req.host != t'.req.host
} for 7

/*
  1121497 vars. 5721 primary vars. 2441489 clauses. 219657ms.
   Solving...
   End solveAll()
   No counterexample found. Assertion may be valid. 2890ms.
*/
check requestIn2Contexts {
	no disj sc,sc':ScriptContext| some r:HTTPRequest | {
		r in (sc.transactions).req
		r in (sc'.transactions).req
	}
} for 10

/*
  104755 vars. 1681 primary vars. 218937 clauses. 122362ms.
   Solving...
   End solveAll()
   Instance found. Predicate is consistent. 1104ms.
*/
run NonStandardMethods{
	some t1,t2,t3:HTTPTransaction | {
//			(t1+t2+t3).req.method in otherMethod 
			t1.cause in XMLHTTPRequest
			t2.cause in XMLHTTPRequest2
			t3.cause in HTTPTransaction
		}

} for 5

/*
The results are:
   #1: .SameOriginRedirectsPossible is consistent.
   #2: .XHR2SimpleToComplexRedirect is consistent.
   #3: No counterexample found. requestIn2Contexts may be valid.
   #4: .NonStandardMethods is consistent.
*/

//FIXME : add how browsers behave on redirects of Options
/*run pfrRedirect {
	some t,t':HTTPTransaction| (t+t').req in PreFlightRequest and t'=t.cause and t.req.to in ATTACKER_SERVER and t'.req.to in SECURE_SERVER
} for 10 but exactly 4 Time
*/



/*
sig L2 extends DNS {} { all l:L2 | #(l.*parent) = 2 }

sig L3 extends DNS {} { all l:L3 | #(l.*parent) = 3 }

run showSubdomain { some l2:L2, l3:L3| isSubdomainOf[l3,l2]} for 4
*/

/*
  55333 vars. 1173 primary vars. 113115 clauses. 122961ms.
   Solving...
   End solveAll()
   Instance found. Predicate is consistent. 319ms.
*/
run showSubdomain { 
    some l2,l3:DNS | {
            isSubdomainOf[l3,l2]
            l3.parent.parent.parent=DNSRoot
            l2.parent.parent= DNSRoot
        }
    } for 4


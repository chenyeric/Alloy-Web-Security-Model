open httpFacts
open redirectionFact
//We have an ordering of time only in this file


one sig Alice extends InternetExplorer {}
one sig Bob extends Firefox {}
one sig Carol extends Safari {}
one sig GOOD,BAD extends HTTPServer {}


fact Traces{

	all t:Time- last | one e:Event | e.pre=t and e.post=t.next
	all e:Event | e.post=e.pre.next


}


check noDeleteRequest{
	no req:HTTPRequest | req.to != req.scriptContext.owner and req.method=DELETE

} for 7 but 1 location, 1 HTTPClient

run show { 
//	some r:HTTPResponse | r.statusCode in RedirectionStatus
//	some t:HTTPTransaction | t.resp.pre!=t.req.post
} for 7 but 1 location, 1 HTTPClient

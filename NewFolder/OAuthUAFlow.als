module OAuth
// User Agent Flow

open declarations

open OAuthCommons


/* 
OA205, p48:
  Use of access token with a matching secret
  At most 1 request with any nonce, time, access token combination
*/  
 
/* "Must know before use" for the private token attributes
Know a token: by generating it or receiving it and having the corresponding key
*/


sig UAFClientInit extends HTTPTransaction {
  clientID: ClientID,
  redirectURI: URI,
  state: lone Token,
  scope: set Token,
  immediate: lone Token, // empty = false
}

fact
{ 
  all req1:UAFClientInit.req|{ 
    // no phishing
    OwnerOfNetworkEndpoint[req1.to] in AuthzServer
  }
}

// User approves manually if imme = false
// Otherwise user is authn'ed by cookie,
// and the user's previous authz decision,
// if not yet expired, is reapplied
sig UAFUserApproval extends HTTPTransaction {
  // request attributes
  clientID: ClientID,
  redirectURI: URI,
  state: lone Token,
  scope: set Token,
  // response attributes
  accessToken: AccessToken,
  refreshToken: RefreshToken,
  
}


fact {
  all req1:UAFUserApproval.req|{
    // no (OwnerOfNetworkEndpoint[req.from] & AuthzServer)
    // no phishing 
    OwnerOfNetworkEndpoint[req1.to] in AuthzServer
  }
}


sig UAFClientAccessResource extends HTTPRequest {
  accessToken:  AccessToken,
}

run show{}

/*
pred isUAFlow[ e1:UAFClientInit, 
    e2:UAFServerChallenge, 
    e3:UAFUserApproval, 
    e4:UAFClientReqCodes,
    e5:UAFServerRespCodes ]{
      one t1:HTTPTransaction|{t1.req=e1 and t1.resp=e2}
      e2.userCode=e3.userCode
      // Assume the user only reads from its own device
      OwnerOfNetworkEndpoint[e1.from]= 
      OwnerOfNetworkEndpoint[e3.from] 
      e4.clientID=e1.clientID 
      e4.verificationCode=e2.verificationCode
      one t2:HTTPTransaction|{
        t2.req=e4 and t2.resp=e5
      }
}


run isModelConsistent{
   some  e1:UAFClientInit, e2:UAFServerChallenge, 
    e3:UAFUserApproval, e4:UAFClientReqCodes,
    e5:UAFServerRespCodes| {
      isDeviceFlow[e1,e2,e3,e4,e5]
      (e3.to & HTTPServer).owner not in WEBATTACKER
      e4.from = e1.from 
      e4.to = e1.to
      no ( ((e1.from & HTTPClient).owner) & ((e1.to & HTTPServer).owner) )         
  }
}
for 8 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER, 5 WebPrincipal

pred UAFSessionFixation[e5:UAFServerRespCodes]{
  some e1:UAFClientInit, e2:UAFServerChallenge, 
    e3:UAFUserApproval, e4:UAFClientReqCodes|
  {
    isDeviceFlow[e1,e2,e3,e4,e5]
    Mallory not in (e1.clientID.client)
    Mallory in (e5.to & HTTPClient).owner + (e5.to & HTTPServer).owner
  }
}


pred containsSecret[e:NetworkEvent, i:Secret]{
  // for the time being, focus on messages in the protocol
  // rather than generic HTTP messages
  e in UAFClientInit+UAFServerChallenge+UAFUserApproval+
       UAFClientReqCodes+UAFServerRespCodes

  all e1:(UAFClientInit&e) | {e1.clientID=i}

  all e2:(UAFServerChallenge&e) | {
    e2.verificationCode=i or
    e2.userCode = i
  }

  all e3:(UAFUserApproval&e) | {e3.userCode=i}

  all e4:(UAFClientReqCodes&e) | {
    e4.clientID = i or
    e4.verificationCode=i 
  }

  all e5:(UAFServerRespCodes&e) | {
    (e5.accessToken) = i or
    e5.refreshToken=i
  }
}

pred knowsSecret[ p:Principal, i:Secret, e:Event ]{
  p in i.madeBy or
  some sourceOfSecret[i, e]
}

fun sourceOfSecret[i:Secret, e:Event ]:NetworkEvent{{
  e1:NetworkEvent|{
    happensBefore[e1,e]
    containsSecret[e1,i]
    some 
      ((e.from & HTTPClient).owner + (e.from & HTTPServer).owner) &
      ( (e1.to & HTTPClient).owner + (e1.to & HTTPServer).owner)
  }
}}

fact mustKnowSecretBeforeUse {
  all e:NetworkEvent, i:Secret|
    containsSecret[e,i] implies{ 
      e in UAFUserApproval or 
      some p:Principal|{
      { 
        p in 
        (e.from & HTTPClient).owner +
        (e.from & HTTPServer).(HTTPServer<:owner) 
        knowsSecret[p,i,e]
      }
    }
  }  
}

// run OAFindAttacks for 8 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER
check OANoAttacks {
  all e5:UAFServerRespCodes|not UAFSessionFixation[e5]
}
for 8 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER, 5 WebPrincipal

// Constrain the web model in this module for better illustration.
// The general model does not enforce this.
fact OAHTTPFacts{
  one Alice
  one Mallory
  all req:HTTPRequest | req.to in HTTPServer
  all user:WebPrincipal | user.servers in HTTPServer
  all t1:HTTPTransaction | some (t1.resp) implies (t1.req.from = t1.resp.to ) and (t1.req.to = t1.resp.from)
  Mallory.servers in (HTTPServer)
  // We don't consider phishing in this model
  all e3:UAFUserApproval | 
      (e3.from & HTTPClient).owner = Alice and e3.to.(HTTPServer<:owner) in AuthzServer
  all e2:UAFServerChallenge | e2.from.(HTTPServer<:owner)  in AuthzServer
  all e5:UAFServerRespCodes | {
    e5.from.(HTTPServer<:owner) in AuthzServer and 
    no ((e5.from & HTTPServer).owner & ((e5.to & HTTPClient).owner + (e5.to & HTTPServer).owner))
  }
  all e1:UAFClientInit| {
    no (AuthzServer & e1.clientID.client) and 
    no ((e1.from & HTTPClient).owner & (e1.to & HTTPServer).owner)
  }
}

*/

/*
- Confused deputy problem:
can the attacker create/modify a req/resp and 
cause the client/authz server to accept it
- use of realm/scope?
*/


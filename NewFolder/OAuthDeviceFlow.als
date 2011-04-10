module OAuth

open declarations

open browserFacts
open OAuthCommons

/* 
OA205, p48:
  At most 1 request with any nonce, time, access token combination
*/  
 
/* "Must know before use" for the private token attributes
Know a token: by generating it or receiving it and having the corresponding key
*/

/* Device profile
   Client -> Authz Server -> Client (c401)
   Client -> User -> Authz Server 
   Client -> Authz Server
*/
  
// Device Flow
sig DFClientInit extends HTTPRequest {
  clientID: ClientID
}

fact
{ 
  all req:DFClientInit|{ 
    // req.clientID.madeBy = OwnerOfNetworkEndpoint[req.from]
    // no phishing
    OwnerOfNetworkEndpoint[req.to] in AuthzServer
  }
}

sig DFServerChallenge extends HTTPResponse {
  verificationCode: VerificationCode,
  userCode: UserCode,
  verificationURI: URI
}

fact { 
  all resp:DFServerChallenge|{
    resp.verificationCode.madeBy in AuthzServer
    resp.userCode.madeBy in AuthzServer
  }
}

sig DFUserApproval extends HTTPRequest {
  userCode: UserCode
}

fact {
  all req:DFUserApproval|{
    // no (OwnerOfNetworkEndpoint[req.from] & AuthzServer)
    // no phishing 
    OwnerOfNetworkEndpoint[req.to] in AuthzServer
  }
}

sig DFClientReqCodes extends HTTPRequest {
  clientID: ClientID,
  verificationCode: VerificationCode
}

fact {
  all req:DFClientReqCodes|{
    // no (OwnerOfNetworkEndpoint[req.from] & AuthzServer)
    // no phishing 
    OwnerOfNetworkEndpoint[req.to] in AuthzServer
  }
}


sig DFServerRespCodes extends HTTPResponse {
//  accessToken: (DFServerRespCodes+DFClientAccessResource) -> AccessToken,
  accessToken:  AccessToken,
  expiry: Time,
  refreshToken: RefreshToken
}

fact { 
  all resp:DFServerRespCodes| {
    resp.accessToken.madeBy in AuthzServer
    resp.refreshToken.madeBy in AuthzServer
  }
}


// sig  accessToken in {{DFServerRespCodes+DFClientAccessResource} -> AccessToken} {}

sig DFClientAccessResource extends HTTPRequest {
  accessToken:  AccessToken,
}


pred isDeviceFlow[ e1:DFClientInit, 
    e2:DFServerChallenge, 
    e3:DFUserApproval, 
    e4:DFClientReqCodes,
    e5:DFServerRespCodes ]{
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
   some  e1:DFClientInit, e2:DFServerChallenge, 
    e3:DFUserApproval, e4:DFClientReqCodes,
    e5:DFServerRespCodes| {
      isDeviceFlow[e1,e2,e3,e4,e5]
      (e3.to & HTTPServer).owner not in WEBATTACKER
      e4.from = e1.from 
      e4.to = e1.to
      no ( ((e1.from & HTTPClient).owner) & ((e1.to & HTTPServer).owner) )         
  }
}
for 8 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER, 5 WebPrincipal

pred DFSessionFixation[e5:DFServerRespCodes]{
  some e1:DFClientInit, e2:DFServerChallenge, 
    e3:DFUserApproval, e4:DFClientReqCodes|
  {
    isDeviceFlow[e1,e2,e3,e4,e5]
    Mallory not in (e1.clientID.client)
    Mallory in (e5.to & HTTPClient).owner + (e5.to & HTTPServer).owner
  }
}


pred containsSecret[e:NetworkEvent, i:Secret]{
  // for the time being, focus on messages in the protocol
  // rather than generic HTTP messages
  e in DFClientInit+DFServerChallenge+DFUserApproval+
       DFClientReqCodes+DFServerRespCodes

  all e1:(DFClientInit&e) | {e1.clientID=i}

  all e2:(DFServerChallenge&e) | {
    e2.verificationCode=i or
    e2.userCode = i
  }

  all e3:(DFUserApproval&e) | {e3.userCode=i}

  all e4:(DFClientReqCodes&e) | {
    e4.clientID = i or
    e4.verificationCode=i 
  }

  all e5:(DFServerRespCodes&e) | {
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
      e in DFUserApproval or 
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
  all e5:DFServerRespCodes|not DFSessionFixation[e5]
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
  all e3:DFUserApproval | 
      (e3.from & HTTPClient).owner = Alice and e3.to.(HTTPServer<:owner) in AuthzServer
  all e2:DFServerChallenge | e2.from.(HTTPServer<:owner)  in AuthzServer
  all e5:DFServerRespCodes | {
    e5.from.(HTTPServer<:owner) in AuthzServer and 
    no ((e5.from & HTTPServer).owner & ((e5.to & HTTPClient).owner + (e5.to & HTTPServer).owner))
  }
  all e1:DFClientInit| {
    no (AuthzServer & e1.clientID.client) and 
    no ((e1.from & HTTPClient).owner & (e1.to & HTTPServer).owner)
  }
}

/*
- Confused deputy problem:
can the attacker create/modify a req/resp and 
cause the client/authz server to accept it
- use of realm/scope?
*/

/* check ...
for 8 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER, 5 WebPrincipal

With the assumption that the user only reads the UserCode
from his/her private device, then the model doesn't
return an attack.

  Solver=minisat(jni) Bitwidth=4 MaxSeq=7 SkolemDepth=1 Symmetry=20
   Generating CNF...
   Generating the solution...
   Begin solveAll()
   308458 vars. 5924 primary vars. 681142 clauses. 267342ms.
   Solving...
   End solveAll()
   No counterexample found. Assertion may be valid. 365ms.
*/

/* Check ...
for 9 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER, 5 WebPrincipal

  Solver=minisat(jni) Bitwidth=4 MaxSeq=7 SkolemDepth=1 Symmetry=20
   Generating CNF...
   Generating the solution...
   Begin solveAll()
   424638 vars. 7304 primary vars. 950178 clauses. 275220ms.
   Solving...
   End solveAll()
   No counterexample found. Assertion may be valid. 588ms.
*/

/* Check ...
for 10 but exactly 0 ACTIVEATTACKER, exactly 0 PASSIVEATTACKER, 5 WebPrincipal

   Solver=minisat(jni) Bitwidth=4 MaxSeq=7 SkolemDepth=1 Symmetry=20
   Generating CNF...
   Generating the solution...
   Begin solveAll()
   564142 vars. 8830 primary vars. 1274757 clauses. 279436ms.
   Solving...
   End solveAll()
   No counterexample found. Assertion may be valid. 897ms.
*/

module OAuth

open declarations
open OAuthCommons

/* 
  The Web Server profile is defined in both OAuth WRAP spec and the OAuth 2.0 core spec 
 */
 
/* "Must know before use" for the private token attributes
Know a token: by generating it or receiving it and having the corresponding key
*/

// Client initiates the Web Server flow by redirecting to Authz Server
sig WSPClientInit extends HTTPTransaction {
  // for WS profile, the response type is hardcoded to "code" for authz code
  clientID: ClientID,
  redirectURI: URI,
  scope: set Token,
  state: lone Token,
}

/*
fact
{ 
  all t1:WSPClientInit |{ 
    // no phishing
    AuthzServer in 
    OwnerOfNetworkEndpoint[t1.redirectURI.host] in AuthzServer
  }
}
*/

sig WSPUserApproval extends HTTPTransaction {
  // request attributes
  clientID: ClientID,
  redirectURI: URI,
  scope: set Token,
  state: lone Token,
  // response attributes
  authzCode: AuthzCode,
}


fact {
  all t1:WSPUserApproval|{
    // user authentication
    t1.authzCode.userId = 
      t1.req.from.(HTTPClient<:owner)+
      t1.req.from.(HTTPServer<:owner)
    // no phishing 
    t1.req.to in AuthzServer
  }
}

// invoke Client callback
sig WSPClientCallback extends HTTPTransaction {
  // request attributes
  redirectURI: URI,
  state: lone Token,
  scope: set Token,
  authzCode: AuthzCode,
}

// Client requests access token
sig WSPReqAccessToken extends HTTPTransaction {
  // request attributes
  // grant type is hard coded to authz_code for Web Server flow
  clientID: ClientID,
  scope: set Token,
  authzCode: AuthzCode,
  redirectURI: URI,

  clientSecret: ClientSecret,
  //  response attributes
  accessToken:  AccessToken,
  expiresIn:  Token,
  refreshToken:  lone RefreshToken,
}

sig WSPClientAccessResource extends HTTPRequest {
  accessToken:  AccessToken,
}

// check for session integrity violation
pred possibleIntegrityViolation[t4:WSPReqAccessToken] {
   some  t1:WSPClientInit, 
    t2:WSPUserApproval, t3:WSPClientCallback
    | {
      // causal chain
      t2.cause = t1 and 
      t3.cause = t2 and 
      t4.protocolPrecursor = t3 and 
      // same browser
      t1.req.from in Browser and
      t1.req.from = t2.req.from and 
      t2.req.from = t3.req.from and 
      // same client
      t1.req.to in HTTPServer and
      t1.req.to not in AuthzServer and
      t1.req.to = t3.req.to and 
      t3.req.to = t4.req.from and 
      // same Authz Server
      t2.req.to = t4.req.to and
      t2.req.to in AuthzServer and
      // t3.req.from.neOwner in WEBATTACKER
      some involvedNetworkEndpoints[t4].neOwner & WEBATTACKER
  }
}

check OANoAttacks {
  all t4:WSPReqAccessToken|not possibleIntegrityViolation[t4]
}
for 8 but exactly 1 AuthzServer, exactly 0 ACTIVEATTACKER, 
exactly 0 PASSIVEATTACKER, 5 WebPrincipal


run isModelConsistent{
   some  t1:WSPClientInit, 
    t2:WSPUserApproval, t3:WSPClientCallback,
    t4:WSPReqAccessToken| {
      // causal chain
      t2.cause = t1 and 
      t3.cause = t2 and 
      t4.protocolPrecursor = t3 and 
      // same browser
      t1.req.from in Browser and
      t1.req.from = t2.req.from and 
      t2.req.from = t3.req.from and 
      // same client
      t1.req.to in HTTPServer and
      t1.req.to not in AuthzServer and
      t1.req.to = t3.req.to and 
      t3.req.to = t4.req.from and 
      // same Authz Server
      t2.req.to = t4.req.to and
      t2.req.to in AuthzServer and 
      some involvedNetworkEndpoints[t4]
  }
}
for 8 but exactly 1 AuthzServer, exactly 0 ACTIVEATTACKER, 
exactly 0 PASSIVEATTACKER, 5 WebPrincipal



/*
pred WSPSessionFixation[e5:WSPServerRespCodes]{
  some e1:WSPClientInit, e2:WSPServerChallenge, 
    e3:WSPUserApproval, e4:WSPClientCallback|
  {
    isDeviceFlow[e1,e2,e3,e4,e5]
    Mallory not in (e1.clientID.client)
    Mallory in (e5.to & HTTPClient).owner + (e5.to & HTTPServer).owner
  }
}


pred containsSecret[e:NetworkEvent, i:Secret]{
  // for the time being, focus on messages in the protocol
  // rather than generic HTTP messages
  e in WSPClientInit+WSPServerChallenge+WSPUserApproval+
       WSPClientCallback+WSPServerRespCodes

  all e1:(WSPClientInit&e) | {e1.clientID=i}

  all e2:(WSPServerChallenge&e) | {
    e2.authzCode=i or
    e2.userCode = i
  }

  all e3:(WSPUserApproval&e) | {e3.userCode=i}

  all e4:(WSPClientCallback&e) | {
    e4.clientID = i or
    e4.authzCode=i 
  }

  all e5:(WSPServerRespCodes&e) | {
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
      e in WSPUserApproval or 
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
  all e5:WSPServerRespCodes|not WSPSessionFixation[e5]
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
  all e3:WSPUserApproval | 
      (e3.from & HTTPClient).owner = Alice and e3.to.(HTTPServer<:owner) in AuthzServer
  all e2:WSPServerChallenge | e2.from.(HTTPServer<:owner)  in AuthzServer
  all e5:WSPServerRespCodes | {
    e5.from.(HTTPServer<:owner) in AuthzServer and 
    no ((e5.from & HTTPServer).owner & ((e5.to & HTTPClient).owner + (e5.to & HTTPServer).owner))
  }
  all e1:WSPClientInit| {
    no (AuthzServer & e1.clientID.client) and 
    no ((e1.from & HTTPClient).owner & (e1.to & HTTPServer).owner)
  }
}

*/


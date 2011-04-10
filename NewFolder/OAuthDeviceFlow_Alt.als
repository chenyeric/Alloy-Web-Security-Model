module OAuth

open declarations

// Bearer access token
// Access token with matching secret


sig Nonce extends Secret {}

sig SecretType extends Token {}

sig Key extends Secret {}

sig SigningKey extends Key {}


sig Algorithm extends Token {}

sig HMACSha256 extends SecretType {}

enum Port{P80,P443}

sig URI {
  host: DNS,
  port: Port,
  path: Path
}

sig Signature extends Token {
  private time: Time,
  private nonce: Nonce,
  private algorithm: Algorithm,
  private method: Method,
  private uri: URI,
  private key: SigningKey
}

sig AccessToken extends Secret {
  secretType: lone SecretType,
  secret: lone Secret
}

sig OAWWWAuthnHeader extends WWWAuthnHeader{
  realm: Token,
  userURI: URI,
  tokenURI: URI, 
  algorithm: Algorithm,
  scope: set URI,
  error: Token
}{
}


sig AuthzHeader extends HTTPRequestHeader {
  token: AccessToken,
  nonce: Nonce,
  time: Time,
  algorithm: Algorithm,
  signature: Signature }
  

/* 
OA205, p48:
  At most 1 request with any nonce, time, access token combination
*/  
 
/* "Must know before use" for the private token attributes
Know a token: by generating it or receiving it and having the corresponding key
*/

/* Device profile
   Client -> Authz Server -> Client (c401)
   Client -> User -> Authz Server -> User
   User -> Client -> Authz Server
*/
  
// Device Flow
//sig Client extends WebPrincipal {}

sig ClientID extends Secret{
  client:WebPrincipal,  
  users:set WebPrincipal // each device is associated with a set of end users
}

sig DFClientInit extends HTTPRequest {
  clientID: ClientID
}

fact
{ 
  all req:DFClientInit+DFClientReqCodes| 
    let o=(req.from & HTTPClient).owner+(req.from & HTTPServer).owner|{
    o in (req&DFClientInit).clientID.madeBy +  (req&DFClientReqCodes).clientID.madeBy and
    // clientID is secret and is known only by its owner and the authz server
    o in  (req&DFClientInit).clientID.client +  (req&DFClientReqCodes).clientID.client
  }
}

sig VerificationCode extends Secret {}

//sig UserCode extends Secret {}

sig DFServerChallenge extends HTTPResponse {
  verificationCode: VerificationCode,
  // only send userCode within an authenticated end-user session
  // userCode: UserCode,
  verificationURI: URI
}

fact { 
  all resp:DFServerChallenge|{
    resp.verificationCode.madeBy = (resp.from & HTTPServer).owner
    // resp.userCode.madeBy = (resp.from & HTTPServer).owner
  }
}

sig DFUserApproval extends HTTPRequest {
  verificationCode: VerificationCode,
  // userCode: UserCode
}

/*
sig DFServerChallenge2 extends HTTPResponse {
  userCode: UserCode,
}

fact { 
  all resp:DFServerChallenge2|{
    resp.userCode.madeBy = (resp.from & HTTPServer).owner
  }
}

sig DFUserApproval2 extends HTTPRequest {
  userCode: UserCode
}
*/

sig DFClientReqCodes extends HTTPRequest {
  clientID: ClientID,
  verificationCode: VerificationCode
}

sig RefreshToken extends Secret {}

sig DFServerRespCodes extends HTTPResponse {
//  accessToken: (DFServerRespCodes+DFClientAccessResource) -> AccessToken,
  accessToken:  AccessToken,
  expiry: Time,
  refreshToken: RefreshToken
}

fact { 
  all resp:DFServerRespCodes| {
    (resp.accessToken).madeBy = (resp.from & HTTPServer).owner
    resp.refreshToken.madeBy = (resp.from & HTTPServer).owner
  }
}

sig AuthzServer extends WebPrincipal{}

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
      e2.verificationCode=e3.verificationCode
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
  all e1:(DFClientInit&e) | {e1.clientID=i}

  all e2:(DFServerChallenge&e) | {
    e2.verificationCode=i // or
    // e2.userCode = i
  }

  all e3:(DFUserApproval&e) | {
    // e3.userCode=i
    e3.verificationCode=i
  }

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
  some e1:NetworkEvent|{
    happensBefore[e1,e]
    containsSecret[e1,i]
    { 
      (e1.to & HTTPClient).owner = p or 
      (e1.to & HTTPServer).(HTTPServer<:owner) = p
    }
  }
}

fact mustKnowSecretBeforeUse {
  all e:NetworkEvent, i:Secret|
    containsSecret[e,i] implies{ 
      // i in UserCode or
      some p:Principal|{
      { 
        p in 
        (e.from & HTTPClient).(HTTPClient<:owner) +
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


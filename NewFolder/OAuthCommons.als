module OAuth

open declarations
open browserFacts

/* Assumptions:
1. The authz server is benign.
Suppose not, then the authz server can issue arbitrary access
tokens that are trusted by the clients. The clients can in turn
use them to retrieve end-users' data. I.e., the authz system
will be totally broken.
2. There is no phishing.
The anti-phishing measures seem to be orthogonal to the 
oauth protocol. 
As a result of this assumption, we can assume the clients
and the end-users interact with the authz server directly.
*/

sig Nonce extends Secret {}

sig SecretType extends Token {}

sig Key extends Secret {}

sig SigningKey extends Key {}


sig Algorithm extends Token {}

sig HMACSha256 extends SecretType {}

enum Port{P80,P443}

sig URI {
  origin: Origin, // schema://host:(port) 
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
  aTSecretType: lone SecretType,
  aTSecret: lone Secret,  // secret assoc'ed with access token
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
  

// owner of the Network Endpoint
fun OwnerOfNetworkEndpoint[ne: NetworkEndpoint]:Principal{
  ( (ne & HTTPClient).owner + (ne & HTTPServer).owner)
}

sig ClientID extends Token {
  client:WebPrincipal,  
  users:set WebPrincipal // each device is associated with a set of end users
}

sig ClientSecret extends Secret {
  clientID:ClientID
}

sig RefreshToken extends Secret {}

// Deprecated. Terminology used in WRAP and OAuth 2.0 specs before draft 8
// sig VerificationCode extends Secret {}

// terminology used in OAuth 2.0 specs draft 8
sig AuthzCode extends Secret {
  private redirectURI : URI
}

sig UserCode extends Secret {}

sig AuthzServer extends HTTPServer {}

/*
sig ResponseType extends Token{}
sig AuthzCodeType extends ResponseType {}
*/
fun involvedNetworkEndpoints[t:HTTPTransaction]:set NetworkEndpoint{
( 
  (t.*cause & HTTPTransaction).req.from + 
  (t.*cause & HTTPTransaction).resp.from + 
  (t.*protocolPrecursor & HTTPTransaction).req.from + 
  (t.*protocolPrecursor & HTTPTransaction).resp.from + 
  (t.*cause & HTTPTransaction).req.to + 
  (t.*cause & HTTPTransaction).resp.to + 
  (t.*protocolPrecursor & HTTPTransaction).req.to + 
  (t.*protocolPrecursor & HTTPTransaction).resp.to + 
  getPrincipalFromOrigin[(transactions.t).owner].servers 
)
}



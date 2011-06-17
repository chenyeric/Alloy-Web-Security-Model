open cookieSigs as c
open util/boolean as b
open SOPDeclarations

sig FrameWithCookieSOP extends Frame {
    didSetCookie : set Cookie, -- the defaultOrigin of this frame set these cookies
    serverReceivesCookie : set Cookie, -- the remote server for the defaultOrigin of this frame DOM receives this cookie with each HTTPRequest
    canReadCookieViaJS : set Cookie, -- these are the cookies that this frame can read (whether for legit use or maliciously) 
    canDeleteCookie : set Cookie, -- these are the cookies an attacking frame can delete
    canOverwriteCookie : set Cookie, -- these are the cookies an attacking frame can overwrite
}


fact OnlyOneFrameSetsEachCookie {
   didSetCookie in  FrameWithCookieSOP one -> set Cookie
}

fact NoCookiesWithSameNameDomainPath {
    no disj c1,c2:Cookie, f:FrameWithCookieSOP | {
         ((c1+c2) in f.serverReceivesCookie or (c1+c2) in f.canReadCookieViaJS) 
         c1.name = c2.name
         c1.domain = c2.domain
         c1.path = c2.path 
    }
}

-- can origin o have set the original cookie?
pred canSetCookieTest[o:Origin, c:Cookie] {
     DomainInCookieScope[o.dnslabel, c]
}

pred serverReceivesCookieTest [o:Origin, c:Cookie] {
      o.schema != DATA and 
      { (o.schema = HTTPS and DomainInCookieScope[o.dnslabel, c]) or
        (o.schema = HTTP and DomainInCookieScope[o.dnslabel, c] and isFalse[c.secure])
      }
}

fact CookieSetConstraints {
  all f:FrameWithCookieSOP, c:Cookie | { 
      c in f.didSetCookie => (canSetCookieTest[f.dom.defaultOrigin, c]  and c.setBy = f.dom.defaultOrigin)
      c in f.serverReceivesCookie => serverReceivesCookieTest[f.dom.defaultOrigin, c] 
      c in f.canReadCookieViaJS => (serverReceivesCookieTest[f.dom.defaultOrigin, c] and isFalse[c.httponly])
      // due to cookie jar overflow, there are no constraints to canDeleteCookie
      c in f.canOverwriteCookie => canSetCookieTest[f.dom.defaultOrigin, c] 
  }
}

check noJSAccessOfHTTPonly {
    no c:Cookie | {
        isTrue[c.httponly]
        some canReadCookieViaJS.c 
    }
} for 10

check noHTTPAccessOfSecure {
    no c:Cookie | {
        isTrue[c.secure]
        some f:canReadCookieViaJS.c | f.dom.defaultOrigin.schema = HTTP
    }
} for 10
 
run siblingdomainOverwriteExists {
   some disj f1,f2: FrameWithCookieSOP, c:Cookie | {
      isSiblingDomainOf[f1.dom.defaultOrigin.dnslabel, f2.dom.defaultOrigin.dnslabel]
      c in f1.didSetCookie
      c in f2.canOverwriteCookie
   }
} for 3

run siblingDomainConfusionExists {
   some disj f1,f2: FrameWithCookieSOP, c1,c2:Cookie | {
      isSiblingDomainOf[f1.dom.defaultOrigin.dnslabel, f2.dom.defaultOrigin.dnslabel]
      c1 in f1.didSetCookie //c1 and c2 made by different frames, with related subdomains
      c2 in f2.didSetCookie
      isTrue[c1.secure]
      isTrue[c1.httponly]
      c1.name = c2.name
      c1.value != c2.value
      c1 in f1.serverReceivesCookie //c1 and c2 are both received by f1's server
      c2 in f1.serverReceivesCookie
   }
} for 4


run httpClobberingSecureCookie {
   some disj f1,f2: FrameWithCookieSOP, c:Cookie | {      
       c in f1.didSetCookie
       c in f2.canOverwriteCookie
       isTrue[c.secure]
       f1.dom.defaultOrigin.dnslabel != f2.dom.defaultOrigin.dnslabel
       f1.dom.defaultOrigin.schema = HTTPS
       f2.dom.defaultOrigin.schema = HTTP
   }
}
for 3 but 0 scriptDOM

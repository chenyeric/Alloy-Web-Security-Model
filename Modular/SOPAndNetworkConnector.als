open basicDeclarations
open SOPDeclarations


sig FrameOnNetwork extends Frame {
   	context: one BrowsingContext
}

//bijection beween FrameWithNetwork and BrowsingContext
fact OneFramePerBC {
   no b:BrowsingContext | no b.~context  //onto 
   context in FrameOnNetwork one -> one BrowsingContext //one-to-one
}

fact FrameOriginIsContextOwner {
   all fn : FrameOnNetwork | {
        some fn.dom.effectiveOrigin => fn.context.owner = fn.dom.effectiveOrigin
        no fn.dom.effectiveOrigin => fn.context.owner = fn.dom.defaultOrigin
   }
}

fact BrowserSOPEnforcerRelation {
   all fn : FrameOnNetwork | {
       fn.context.location in InternetExplorer6 iff fn.enforcer = IE6SOP
       fn.context.location in InternetExplorer7 iff fn.enforcer = IE7SOP
       fn.context.location in InternetExplorer7 iff fn.enforcer = IE8SOP
       fn.context.location in Firefox2 iff fn.enforcer = Firefox2SOP
	   fn.context.location in Firefox3 iff fn.enforcer = Firefox3SOP
       fn.context.location in Firefox4 iff fn.enforcer = Firefox4SOP
       fn.context.location in Safari iff fn.enforcer = SafariSOP
       fn.context.location in Chrome iff fn.enforcer = ChromeSOP
	   fn.context.location in Opera iff fn.enforcer = OperaSOP
       fn.context.location in Android iff fn.enforcer = AndroidSOP
      
   }
}

//----------------SSL ------------/
fact HTTPSIsLinkedWithCertificate{

	all fn:FrameOnNetwork|{
		HTTPS = fn.dom.effectiveOrigin.schema implies {
			some fn.context.transactions.cert
		}
	}

}

run {some p:FrameOnNetwork|some p} 
for 6

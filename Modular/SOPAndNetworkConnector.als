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

//transactions initiated by a frame should equal to all transactions caused by the resources in that frame
fact AllTransactionsAreSane{
	all fn:FrameOnNetwork|{
		//TODO: add more resources here
		(fn.dom.transaction+fn.scripts.transaction)=fn.context.transactions
	}

}

//----------------SSL ------------/
fact HTTPSIsLinkedWithCertificate{

	all dom:documentDOM|{
		HTTPS = dom.effectiveOrigin.schema iff { 
			some dom.transaction.cert
		}
	}

	all script:scriptDOM|{
		HTTPS = script.srcOrigin.schema iff {
			some script.transaction.cert
		}
	}

	//TODO: include other objects in the future
	
}
// compromised SSL session implies BADCA
fact CompromisedSSLImpliesBadCA{
	all script:scriptDOM, fn:FrameOnNetwork|{
		{
			script in fn.scripts
			fn.dom.effectiveOrigin.dnslabel in GOOD.dnslabels  // if the dom of this element is not compromised (doesn't make sense if it is)
			script.srcOrigin.dnslabel in ACTIVEATTACKER.dnslabels //but if a script is under DNS rebinding attack
		}implies{  //then there must be an active attacker
			BADCA = script.transaction.cert.ca //that changed the cert of the script

		}
	}

}


run {some p:FrameOnNetwork|some p} 
for 6

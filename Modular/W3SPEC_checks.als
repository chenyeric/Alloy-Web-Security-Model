
open W3SPEC_facts

/*
//----------------------------Page Loader CHECKS------------------------------------/

//there should be no loops
check NoLoopInParentChildContext{
	no disj pctx,cctx:BrowsingContext|{
		pctx in cctx.^ancestors
		cctx in pctx.^ancestors
	}
}for 5


run unitOfRelatedSimilarOriginBrowsingContext_areSane{
	some ctxa,ctxb:BrowsingContext|{
		some unitctx:UnitOfRelatedSimilarOriginBrowsingContext|{
			(ctxa+ctxb) in unitctx.browsingContexts
			ctxa.activeDocument.origin != ctxb.activeDocument.origin
		}
	}
} for 3

//-----------------------------CHECKS FOR IFRAME + SANDBOX (STATIC DOM)------------------------/
//sandbox navigation policy checker
check NestedAllowNavigationWorks{
	no disj nestedctx, sandboxctx, topctx:BrowsingContext|{
		topctx.isTop = TRUE
		topctx = sandboxctx.parent
		sandboxctx = nestedctx.parent

		NOT_ALLOW_TOP_NAVIGATION in sandboxctx.contextContainer.sandboxPolicies //policy exists to disallow top navigation
		
		topctx in nestedctx.canNavigate // nestedctx can navigate the top
		
	}
} for 5

check NestedAllowSameOriginWorks{
	all disj sandboxctx, ctx, randomctx:BrowsingContext{
		{ 
			sandboxctx in ctx.ancestors  //iframe sandbox sandboxes a frame
			NOT_ALLOW_SAME_ORIGIN in most_strict_sandbox_policy[sandboxctx.contextContainer] //but the sandbox is put into a unique origin
		}implies{ //then the embedded frame must also be in a unique origin
			ctx.activeDocument.effectiveScriptOrigin != randomctx.activeDocument.effectiveScriptOrigin  
			ctx.activeDocument.effectiveScriptOrigin != randomctx.activeDocument.origin
		}
	}
}for 7


check NestedAllowScriptPolicyWorks{
	all disj sandboxctx, ctx:BrowsingContext{
		{			
			sandboxctx in ctx.ancestors  //iframe sandbox sandboxes a frame
			NOT_ALLOW_SCRIPTS in most_strict_sandbox_policy[sandboxctx.contextContainer] //but the sandbox has scripts disabled
		}implies
			no (ctx.activeDocument.elements & ScriptElement) //then the frame must also have scripts disabled
	}
}for 7



// ============================CHECK FOR JAVASCRIPT (DYNAMIC DOM)====================/

run DomManipulationEventsAreSane{
	some disj dme1,dme2:DomManipulationEvent|{
		no dme1.oldElement
		no dme2.newElement
	}
}for 5


check scriptObject_BypassIframeSandboxPopup{
	all oldfrm, newfrm:IframeElement, dme:DomManipulationEvent | {
		{
			//new frame is created from old frame vs some script
			newfrm = dme.newElement
			oldfrm = dme.oldElement	
			some oldfrm.sandboxPolicies //old frame is sandboxed
			((oldfrm.nestedContext = dme.script.browsingContext) or (oldfrm.nestedContext in dme.script.browsingContext.ancestors))
		}implies {
			no newfrm.nestedContext.opened //the new frame cannot open any popups
		}
	}
}for 6

check postMessageConfidentiality{
	no pme: postMessageEvent{
		some doc_src, doc_dest:Document{
			doc_src.effectiveScriptOrigin != pme.source.browsingContext.activeDocument.effectiveScriptOrigin
			doc_dest.effectiveScriptOrigin != pme.destination.browsingContext.activeDocument.effectiveScriptOrigin
			(doc_src in pme.source.browsingContext.activeDocument.*(~oldDoc.newDoc)) or (doc_dest in pme.destination.browsingContext.activeDocument.*(~oldDoc.newDoc))
		}
	}
}for 6


check MetaRefreshesAreSane{

	all doc:Document, meta:METAElement|{
		{
			meta in doc.elements
			REFRESH = meta.http_equiv
		}implies{
			some nav:NavigationEvent|{
				nav.origin = meta.origin
				nav.oldDoc = doc
			}
		}
	}

}for 10


//assume all DOMManipulation event are caused by innerHTML

/*

//Check for script execution in the case of innerhtml
check Innerhtmlnoscript{
    all el : Element |{ 
      el.cause.method = innerhtml =>

     no sc : ScriptObject|{
             sc.executed = TRUE
          }
       }


} for 6


check Innerhtmlnoscript2{
    all el : Element |{ 
      el.cause.method = innerhtml =>

  no ne: NavigationEvent {
    ne.script.executed = TRUE      
  }
       }


} for 6
*/


// ====================6.1.4 Event loops======================/


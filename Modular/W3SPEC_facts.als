open W3SPEC_signatures


//===================================PAGE LOADER ===================/
//you can either have a parent context or an opener context, but not both
fact browsingContext_onlyOneCreator{
	all ctx:BrowsingContext|{
		//every browsing context can only have 1 creator
		some ctx.parent implies (no ctx.opener and ctx.parent = ctx.creator)
		some ctx.opener implies (no ctx.parent and ctx.opener = ctx.creator)
	}
}

//no loops
fact browsingContext_noLoopContext{
	all ctx:BrowsingContext|{
		ctx not in ctx.ancestors
	}
}

//Iframe/browsing context relationship
fact browsingContext_IframeRelationship{
	all ctx:BrowsingContext, iframe:IframeElement|{
		(ctx = iframe.nestedContext) iff (iframe = ctx.contextContainer)
	}
}


fact browsingContext_parentChildRelationship{
	//a is b's parent iff b is a's child
	all cctx,pctx:BrowsingContext|{
		pctx = cctx.parent iff cctx in pctx.children
	}

	//a is b's parent only if b is an iframe inside a
	all cctx,pctx:BrowsingContext|{
		pctx = cctx.parent iff(
			pctx = cctx.~nestedContext.~elements.~activeDocument
		)
	}
}

fact browsingContext_openerRelationship{
	all cctx,pctx:BrowsingContext|{
		pctx = cctx.opener iff cctx in pctx.opened
	}
}

//top browsing context
fact browsingContext_topBrowsingContext{
	all ctx:BrowsingContext|{
		ctx.isTop = TRUE iff(
			no ctx.parent
		)
	}
}

fact browsingContext_linkTopWithChild{
	all ctxa,ctxb:BrowsingContext|{
		{
			ctxa.isTop = TRUE
			ctxb in ctxa.*children
		} implies ctxa = ctxb.top
	}
}

//TODO: name cannot start off with '_'
//fact browsingContext_name{}


//document / BC relationship
fact documentAndBrowsingContext{
	all doc:Document, bc:BrowsingContext|{
		doc in bc.documents iff bc = doc.browsingContext
	}	
}



//describes the relationship between directly nested browsing contexts
fact nestedBrowsingContext{
	all disj pctx,cctx:BrowsingContext|{ // for context A and B
		some doc:Document |{
			some ele:Element |{
				(doc in pctx.documents and //if doc is in A
				 ele in doc.elements and      // if (iframe) element is in doc
				 ele.nestedContext = cctx) iff{ // this (iframe) element contains  B if and only if
					cctx.parentDocument = doc and // B's parent document is doc
					cctx.contextContainer = ele and // B's context container is the (iframe) element
					no cctx.opener
					// pctx doesn't neccessarily have to be cctx's parent, (i.e., if an iframe is removed from the document)
				}
			}
		}
	}
}

//ancestor browsing contexts
fact ancestorBrowsingContext{
	all disj ctx1, ctx2:BrowsingContext|{
		ctx1 = ctx2.*parent iff ctx1 in ctx2.ancestors
	}
}

//fully active browsing context
fact browsingContext_fullyActiveBrowsingContext{
		all ctx:BrowsingContext|{
			ctx.isFullyActive = TRUE iff(
				ctx.isTop = TRUE or
				ctx.parentDocument.browsingContext.isFullyActive = TRUE //does recursion work in alloy?
			)
		}
}


//browser navigation policy ""FOR NO SANDBOX""
//A browsing context A is allowed to navigate a second browsing context B if one of the following conditions is true
//1) Either the origin of the active document of A is the same as the origin of the active document of B, or
//2) The browsing context A is a nested browsing context with a top-level browsing context, and its top-level browsing context is B, or
//3) The browsing context B is an auxiliary browsing context and A is allowed to navigate B's opener browsing context, or
//4) The browsing context B is not a top-level browsing context, but there exists an ancestor browsing context of B whose 
//active document has the same origin as the active document of A (possibly in fact being A itself).
fact browsingContext_Navigation{
	all disj ctxA, ctxB:BrowsingContext|{
		no ctxB.contextContainer.sandboxPolicies implies{
			ctxB in ctxA.canNavigate iff (
				(ctxA.activeDocument.origin = ctxB.activeDocument.origin) or // 1)
				(ctxB in ctxA.ancestors and ctxB.isTop = TRUE) or //2
				(some ctxB.opener and ctxB.opener in ctxA.canNavigate) or //3
				some ctxC:BrowsingContext |{ //4
					ctxC in ctxB.ancestors
					ctxB.isTop = FALSE  
					ctxC.activeDocument.origin = ctxA.activeDocument.origin
				}
			)
		}
	}
}


//Directly reachable browsing contexts are:
//1)The browsing context itself.
//2)All the browsing context's child browsing contexts.
//3)The browsing context's parent browsing context.
//4)All the browsing contexts that have the browsing context as their opener browsing context.
//5)The browsing context's opener browsing context.

fact browsingContext_directlyReachable{
	all ctx:BrowsingContext|{
		ctx.directlyReachable = (ctx + ctx.children + ctx.creator + ctx.opened)
	}
}


//The transitive closure of all the browsing contexts that are directly reachable browsing contexts 
//forms a unit of related browsing contexts.
fact unitOfRelatedBrowsingContext_definition{
	all unitctx:UnitOfRelatedBrowsingContext|{
		all ctxA, ctxB:BrowsingContext|{
			(ctxA + ctxB) in unitctx.browsingContexts iff  (ctxA in ctxB.*directlyReachable)
		}
	}
}



fact unitOfRelatedBrowsingContext_no_duplication{
	no disj unitctxa, unitctxb:UnitOfRelatedBrowsingContext|{
		some ctx:BrowsingContext|{
			ctx in unitctxa.browsingContexts
			ctx in unitctxb.browsingContexts
		}
	}
}

//through appropriate manipulation of the document.domain attribute, could be made to 
//be the same as other members of the group, but could not be made the same as members of 
//any other group
fact unitOfRelatedSimilarOriginBrowsingContext_definition{
	some unitctx: UnitOfRelatedSimilarOriginBrowsingContext|{
		all ctxa, ctxb:BrowsingContext{
			{
				isSubdomainOf[ctxa.activeDocument.origin.dnslabel, ctxb.activeDocument.origin.dnslabel] or
				isSubdomainOf[ctxb.activeDocument.origin.dnslabel, ctxa.activeDocument.origin.dnslabel] or
				isSiblingDomainOf[ctxa.activeDocument.origin.dnslabel, ctxb.activeDocument.origin.dnslabel]
			} iff (ctxa+ctxb) in unitctx.browsingContexts
		}
	}
}

fact OneUnitOfRelatedSimilarOriginBrowsingContextPerOrigin{
	no disj unitctxa, unitctxb: UnitOfRelatedSimilarOriginBrowsingContext|{
		some ctx: BrowsingContext{
			(ctx in unitctxa.browsingContexts) and (ctx in unitctxb.browsingContexts)
		}	
	}
}

fact originOfSimilarBrowsingContext{
	all ctx:BrowsingContext|{
		some unitctx: UnitOfRelatedSimilarOriginBrowsingContext|{
			(ctx.activeDocument.origin.dnslabel.parent in DNSRoot and//top level DNS origin
				ctx in unitctx.browsingContexts) iff ctx.activeDocument.origin = unitctx.origin
		}
	}
}

//TODO: Because they are nested through an element, child browsing contexts are always tied to a 
//specific  Document in their parent browsing context. User agents must not allow the user to interact 
//with child browsing contexts of elements that are in Documents that are not themselves fully active.



//====================================HTML ELEMENTS================/

//the sandbox policies for a frame should be the most strict policy after combining its parents policy
fun most_strict_sandbox_policy[frm:IframeElement]:set iframe_sandbox_policy{
	frm.sandboxPolicies+frm.*(~elements.~activeDocument.contextContainer).sandboxPolicies //union of all the restrictions
}

fact IframeCannotBeTopLevelFrame{
	all frame:IframeElement{
		frame.nestedContext.isTop = FALSE		
	}
}


//iframe sandbox navigation poicy
fact IframeElement_SandboxNavigationPolicy{

	//The sandboxed navigation browsing context flag
	all sandboxfrm:IframeElement , ctx: BrowsingContext|{
		{
			some sandboxfrm.sandboxPolicies //if frame is in a sandbox
			ctx in sandboxfrm.nestedContext.canNavigate  //if sandbox can navigate a context, then...
		} implies(
			ctx = sandboxfrm.nestedContext or//the context is trying to navigate itself
			ctx = sandboxfrm.nestedContext.top //this frame must be the top level frame
		)
	}

	//The sandboxed top-level navigation browsing context flag
	all sandboxfrm:IframeElement , ctx: BrowsingContext|{
		{
			ctx = sandboxfrm.nestedContext.top
			NOT_ALLOW_TOP_NAVIGATION in most_strict_sandbox_policy[sandboxfrm]
		} implies //if allow navi attr is not set
			ctx !in sandboxfrm.nestedContext.canNavigate //then top frame cannot be navigated by sandboxed frame
	}
}


//TODO sandbox plugin flag

//TODO seamless flag

fact IframeElement_SandboxOriginPolicy{
	//if allow same origin is not set, then the sandbox should have its unique origin
	all disj sandboxfrm, frm:IframeElement{
		{
			NOT_ALLOW_SAME_ORIGIN in most_strict_sandbox_policy[sandboxfrm] //if allow same origin is not set
		}implies{
			sandboxfrm.~elements.effectiveScriptOrigin = sandboxfrm.~elements.origin //sandbox cannot set its document.domain
			sandboxfrm.~elements.effectiveScriptOrigin != frm.~elements.effectiveScriptOrigin
			sandboxfrm.~elements.effectiveScriptOrigin != frm.~elements.origin    //sandbox must have its own unique origin
		}
	}
}


fact IframeElement_SandboxScriptPolicy{
	//if allow script is not set, then the sandbox should not have a script element
	all sandboxfrm:IframeElement, script:ScriptElement{
		NOT_ALLOW_SCRIPTS in most_strict_sandbox_policy[sandboxfrm] implies
			script not in sandboxfrm.nestedContext.activeDocument.elements
	}
}

//popups are disabled for iframe sandbox
fact iFrameElement_SandboxCannotOpenPopUps{
	all sandbox_ctx:BrowsingContext|{
		some sandbox_ctx.contextContainer.sandboxPolicies implies
			no sandbox_ctx.opened
	}
}

run topNavigationCanHappen{
		some frm: IframeElement, ctx:BrowsingContext{
			ctx = frm.nestedContext.top
			ctx in frm.nestedContext.canNavigate
		} 
} for 5



//============================JAVASCRIPT ===========================/
//each script tag will have a script object associated with it
fact scriptElement_scriptObject_relationship{
	all scriptEle: ScriptElement, scriptObj:ScriptObject|{
		scriptObj = scriptEle.script iff scriptEle= scriptObj.element
	}
}

//=====================Same Origin Policy
//User agents must raise a SECURITY_ERR exception whenever any 
//properties of a Document object are accessed by scripts whose effective 
//script origin is not the same as the Document's effective script origin.
pred SOP_pass[script:ScriptObject, ele:Element]{
	script.element.host.effectiveScriptOrigin = ele.host.effectiveScriptOrigin
}

// which browsing context is the script belong to?
fact scriptObject_BrowsingContext_relationship{
	all script:ScriptObject, ctx:BrowsingContext|{
		ctx = script.browsingContext iff ctx = script.element.~elements.browsingContext
	}
}


//script can manipulate a dom object if SOP allows it
fact domManipulationEvent_definition{
	all dme: DomManipulationEvent|{
		(some dme.oldElement and some dme.newElement) implies{
			SOP_pass[dme.script,dme.oldElement]
			SOP_pass[dme.script,dme.newElement]
			dme.oldElement != dme.newElement
		}
	}
}

//Only the most recent element is connected with the DOM
fact domManipulationEvent_MostRecentElementConnectedWithDom{
	all ele:Element|{
		some ele.host implies {  //if element is attached with dom
			no ele.~oldElement		// then this must be the most recent version
			no ele.^(cause.oldElement).host  //none of its older versions are attached to DOM
		}
	}
}

fact domManipulationEvent_DOMChangeOnlyOccurOnSameTag{
	all dme: DomManipulationEvent|{
		(some dme.oldElement and some dme.newElement) implies
			dme.oldElement.tag = dme.newElement.tag
	}
}

//=================5.1.6 browsing context keywords
//	func_form_target: BrowsingContext,
fact scriptObject_form_target{
	all ctx:BrowsingContext, script:ScriptObject|{
		ctx = script.func_form_target iff(
			(ctx = script.browsingContext and script.browsingContext.contextContainer.is_seamless = FALSE) or //for non seamless iframes, form target is the current frame
			((ctx = script.browsingContext.parent or ctx = script.browsingContext.opener) and
				script.browsingContext.contextContainer.is_seamless = TRUE) //for seamless iframes, form target is its nearest ancestor
		)
	}
}

//	func_open: BrowsingContext,
fact scriptObject_BrowsingContext_open{
	all ctx:BrowsingContext, script:ScriptObject|{
		ctx = script.func_open iff (
			(ctx.opener = script.browsingContext) and (no script.browsingContext.contextContainer.sandboxPolicies)  //sandbox can't open new window
		)
	}
}


//	func_self: BrowsingContext,
fact scriptObject_BrowsingContext_self{
	all ctx: BrowsingContext, script:ScriptObject|{
		ctx = script.func_self iff ctx = script.browsingContext
	}
}

//	func_blank: BrowsingContext,
fact scriptObject_BrowsingContext_blank{


}


//	func_parent: BrowsingContext,
//	func_top: BrowsingContex


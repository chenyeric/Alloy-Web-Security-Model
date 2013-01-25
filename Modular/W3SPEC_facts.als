open W3SPEC_signatures
open util/ordering[State] as State
open util/ordering[State] as EventState

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


//document / Browsing context relationship
fact documentAndBrowsingContext{
	all doc:Document, bc:BrowsingContext|{
		doc in bc.documents iff bc = doc.browsingContext
	}	
}

//window Browsing context relationship
fact windowAndBrowsingContext{
	all win:Window, ctx:BrowsingContext|{
		win = ctx.window iff ctx = win.browsingContext
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

//using document.domain to set effectivescript origin
fact document_effectiveScriptOrigin{
	all doc: Document|{
		isSubdomainOf[doc.effectiveScriptOrigin.dnslabel, doc.origin.dnslabel]
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

//==========================5.4 SESSION HISTORY AND NAVIGATION=============
fact History_is_unique{
	all disj ctx1,ctx2:BrowsingContext|{
		ctx1.sessionHistory != ctx2.sessionHistory
	}
}

//TODO: model the other rules for the history object

//5.5.1
//locations are unique
fact Location_definition{
	all disj loc1,loc2:Location|{
		loc1.~location != loc2.~location
	}
}

//navigation event via document.location
fact Location_navigation{
	all ne: NavigationEvent |{
		//if navigation is caused by a script, then the following must hold
		some (
			ne.script 
			//TODO: add user interactive navigation here
		) iff(
			ne.script.element.host.effectiveScriptOrigin = ne.oldDoc.effectiveScriptOrigin or
			ne.oldDoc.~activeDocument in ne.script.browsingContext.canNavigate
		)
	}
}

//11.4 Cross-domain messaging
fact postMessage{
	all pe: postMessageEvent|{
		pe.script.element.host.effectiveScriptOrigin = pe.source.browsingContext.activeDocument.effectiveScriptOrigin
	}
}


// ====================6.1.4 Event loops


// Dominatrixss - http://code.google.com/p/dominatrixss-csp/
fact dominatrixss{
	all dme: DomManipulationEvent|{

	}	
}


//6.1 eventloop
<<<<<<< HEAD
=======
//Set up ordered status

>>>>>>> origin/master


fact stateinti{
     State/first.setdocwrite=0 && 
     State/first.setdomcontentloaded =0&&
     State/first.setbrowsingcontext =1 && 
     State/first.seteventlope =1    
}

//doc.write has to be called before the domcontentloaded event
fact domcontentstatus {
     all st: State| st.setdomcontentloade=1 |
     st/prevs.setdocwrite= 1 
}

//If an†event loop's†browsing contexts†all go away, then the†event loop†goes away as well. A†browsing context†always has an†event loop†coordinating its activities
fact eventloopstatus {
     all st:State| st.setbrowsingcontext =0 |
     st/nexts.seteventlope = 0  
}

fact eventstatetransfer {
      all s: EventSate, s': s.next {
      RunEvent [s.eventloop, s'.eventloop]
  }
}

// Running the eventloop till meet the condition 
pred RunEvent [s.eventloop, s'.eventloop: set EventLoop] {
         one x: s.eventloop | {
          s'.eventloop.taskqueue = s.eventloop.taskqueue.delete[0] //delete the executed event from the taskqueue
  }
}

//8.2.6 the end
//Once the user agent stops parsing the document, the user agent //must run the following steps

//Spin the event loop until the first script in the list of //scripts that will execute when the document has finished //parsing has its "ready to be parser-executed" flag set 
 
run RunEvent {s.first!=null&&s.first.readyparserexecute = 1}

//If the list of scripts that will execute when the document has //finished parsing is still not empty, repeat these substeps //again from substep 1.

run RunEvent {s.isEmpty = 1}

//4. Queue a task to fire a simple event that bubbles named DOMContentLoaded at the Document.
// run script in listscriptassoon

//4.3 scripting
//If the element has a src attribute, and the element has a defer //attribute, and the element has been flagged as "parser-  //inserted", and the element does not have an async attribute, //add it to listscriptexecutefinishparse

fact scriptattribute {

   selement : ScriptElement,s1: one listscriptexecutefinishparse,s2:one listscriptpendingparseblock, s3:listscriptinorder, s4:listscriptsoon{

              selement.src != null && selement.defer = 1 && selement.parserinserted = 1 && selement.async != 1  => 
              s1.add[selement]

//If the element has a src attribute, and the element has been //flagged as "parser-inserted", and the element does not have an //async attributeThe element is the pending parsing-blocking //script of the Document of the parser that created the element. //(There can only be one such script per Document at a time.)

              else selement.src != null && selement.parserinserted = 1 && selement.async != 1  => 
              s2.add[selement]

//Yuan: not sure if we need this? If the element does not have a //src attribute, and the element has been flagged as //"parser-/inserted", and either the parser that created the //script is an XML parser or it's an HTML parser whose script //nesting level is not greater than one, and the Document of the //HTML parser or XML parser that created the scriptelement has a //style sheet that is blocking scriptsThe element is the pending //parsing-blocking script of the Document of the parser that //created the element. (There can only be one such script per //Document at a time.)


//If the element has a src attribute, does not have an async //attribute, and does not have the "force-async" flag setThe //element must be added to the end of the list of scripts that //will execute in order as soon as possible associated with the //Document of the script element at the time the prepare a script //algorithm started.
              else selement.src != null && element.async = 0 && element.forceasync = 0 =>
              s3.add[selement]

//If the element has a src attributeThe element must be added to //the set of scripts that will execute as soon as possible of the //Document of the script element at the time the prepare a //scriptalgorithm started.
              else selement.src != null =>
              s4.add[selement]



}
}






open W3SPEC_signatures
/*
open util/ordering[State] as State
open util/ordering[State] as EventState
*/
/*
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


*/
//====================================HTML ELEMENTS================/

fact elements_cannot_have_two_parents{
	all disj parent1,parent2,ele:Element|{
		ele in parent1.children => ele not in parent2.children
	}
}

fact no_cycle_element_chain{
	all ele:Element|{
		ele not in ele.^children
	}
}

fact elements_in_document_are_reachable{
	all element: Element, doc: Document|{
		element in doc.elements => element in doc.root.*children
	}
}

fact parent_and_child_relationship_for_elements{
	all ele:Element, doc:Document|{
		ele in doc.elements iff doc in ele.host
	}
}

//This fact is super confusing, essentially the "host" field is a set 
// of the same document in different point in time
fact element_can_only_belong_to_the_same_document_in_multiple_time_frame{
	all ele:Element, doc:Document|{
		doc in ele.host iff 
		doc.effectiveScriptOrigin = ele.hostEffectiveOrigin
	}
}
/*
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


*/
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
	script.element.hostEffectiveOrigin = ele.hostEffectiveOrigin
}
/*
// which browsing context is the script belong to?
fact scriptObject_BrowsingContext_relationship{
	all script:ScriptObject, ctx:BrowsingContext|{
		ctx = script.browsingContext iff ctx = script.element.~elements.browsingContext
	}
}
*/
/*
//script can manipulate a dom object if SOP allows it
fact domManipulationEvent_definition{
	all dme: DomManipulationEvent|{
		(some dme.oldElement and some dme.newElement) implies{
			SOP_pass[dme.script,dme.oldElement]
			SOP_pass[dme.script,dme.newElement]
			dme.oldElement != dme.newElement
		}
	}
}*/
/*
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
*/
/*
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
			ne.script.element.hostEffectiveOrigin = ne.oldDoc.effectiveScriptOrigin or
			ne.oldDoc.~activeDocument in ne.script.browsingContext.canNavigate
		)
	}
}

//11.4 Cross-domain messaging
fact postMessage{
	all pe: postMessageEvent|{
		pe.script.element.hostEffectiveOrigin = pe.source.browsingContext.activeDocument.effectiveScriptOrigin
	}
}
*/
//====================== Unorganized stuff =======================/
//TODO: organize

fact dmeMustBeCalledFromValidScript{
	all dme:DomManipulationEvent|{
		some doc:Document|{
			dme.script.element in doc.elements
		}
	}
}

//all Document must have an associate state
fact all_doc_must_be_in_state{
	all doc:Document|{
		some s:ParserState|{
			s.document = doc
		}
	}
}

fact InnerHTMLCantInjectScriptTag{
	all dme:DomManipulationEvent, script:ScriptObject|{
		dme.method = innerhtml =>
		script.element not in dme.newElement.*children
	}
}

fact MetaRefreshMustHaveAnOrigin{
	all meta:MetaElement|{
		REFRESH = meta.http_equiv implies some meta.origin
	}
}

//navigation using meta refresh
fact Metarefresh_navigation{
	//given any doc and meta
     all doc:Document, meta:MetaElement|{
		{
			//if the meta element is in the doc
			meta in doc.elements
			//and it has refresh http_equiv attribute
			REFRESH = meta.http_equiv
		}implies{
			//then there must exist a corresponding navigation event
			some navEvent:NavigationEvent|{
				navEvent.origin = meta.origin
				navEvent.oldDoc = doc
			}
		}
    }   
}



//6.1 eventloop

//initial state
fact ParserStarts{
	no first.document.elements
	!first.tokenQueue.eleSeq.isEmpty
}

fact document_write_only_adds_new_node{
	all dme: DomManipulationEvent|{
		dme.method = document_write => 
		no dme.oldElement
	}
}

fact innerHTML_are_sane{
	all dme:DomManipulationEvent|{
		dme.method = innerhtml implies{
			one dme.oldElement 
			one dme.newElement 
			dme.oldElement != dme.newElement
		}
	}
}

pred ParserStep[doc, doc': Document, q, q': TokenQueue]{
	q'.eleSeq = q.eleSeq.rest
	doc'.elements = doc.elements+q.eleSeq.first
	//TODO: we also need to say doc' = doc for everything else
}

pred InnerHTML[doc, doc':Document, ele, ele':Element, q, q':TokenQueue]{

	// the parent node for old element must be in the new document
	ele.~children in doc'.elements
	// old element is not in the new document
	// this implicitly implies its children are not in the new doc
	ele not in doc'.elements

	//the new element's parent is the same as the old element's parent
	ele'.~children = ele.~children

	//the new element is in the new document
	ele' in doc'.elements

	// queue does not change
	q.eleSeq = q'.eleSeq
	

	//TODO: we also need to say doc' = doc is the same for everything else
}

pred Document_write[doc,doc':Document, ele':Element, q,q':TokenQueue]{
	doc = doc'
	q'.eleSeq = q.eleSeq.insert[0,ele']
}

pred NavigationToJsUrl[doc,doc':Document, script:ScriptObject, q,q':TokenQueue]{
	doc=doc'
	q'.eleSeq = q.eleSeq.insert[0,script.element]
}

//parser core
fact parser_core{
	all s: ParserState, s': s.next|{

		//you can only transfer from 1 state to the next by using the following methods

		ParserStep[s.document,s'.document, s.tokenQueue, s'.tokenQueue] or
		some dme:DomManipulationEvent|{
			dme.method = innerhtml
			dme.script = s.tokenQueue.eleSeq.first.script
			dme.oldElement in s.document.elements
			InnerHTML[s.document, s'.document, dme.oldElement, dme.newElement, s.tokenQueue, s'.tokenQueue]
		} or 
		some dme:DomManipulationEvent|{
			dme.method = document_write
			dme.script = s.tokenQueue.eleSeq.first.script
			Document_write[s.document, s'.document, dme.newElement, s.tokenQueue, s'.tokenQueue]
		} or 
		some script:ScriptObject, nav:NavigationEvent|{
			JAVASCRIPT = nav.origin.schema
			nav.oldDoc = s.document
			NavigationToJsUrl[s.document, s'.document, script, s.tokenQueue, s'.tokenQueue]
		}

	}
}
/*
// dom manipulation events
// ============= OBSOLETE =================
fact parser_events{
	all s:ParserState, s':s.next|{

		
		all nav:NavigationEvent|{
			// if a navigation event happens with a JavaScript URL
			JAVASCRIPT = nav.origin.schema implies {
	
				some script:ScriptObject|{
					nav.oldDoc = s.document
					NavigationToJsUrl[s.document, s'.document, script, s.tokenQueue, s'.tokenQueue]
					//TODO: we must say something about the content of the script, which is not currently modeled
					
				}
			}
		}
	
		all domManip: DomManipulationEvent|{
			// if the next script in queue uses innerHTML
			{
				domManip.method = innerhtml
				domManip.script = s.tokenQueue.eleSeq.first.script

				//and if he element it's trying to modify is in our document
				domManip.oldElement in s.document.elements
			}implies{
				InnerHTML[s.document, s'.document, domManip.oldElement, domManip.newElement, s.tokenQueue, s'.tokenQueue]
			}
			
			//if the next script in queue uses document.write
			{
				domManip.method = document_write
				domManip.script = s.tokenQueue.eleSeq.first.script
			}implies{
				Document_write[s.document, s'.document, domManip.newElement, s.tokenQueue, s'.tokenQueue]
			}
		}
	}
}*/

fact element_on_queue_are_unique{
	all s:ParserState|{
		!s.tokenQueue.eleSeq.hasDups
	}
}

//======== innerHTML Can't inject script test=======/

fact all_dme_are_innerHTML{
	all dme:DomManipulationEvent|{
		dme.method = innerhtml
	}
}



//navigation using meta refresh
fact Metarefresh_navigation{
	//given any doc and meta
     all doc:Document, meta:MetaElement|{
		{
			//if the meta element is in the doc
			meta in doc.elements
			//and it has refresh http_equiv attribute
			REFRESH = meta.http_equiv
		}implies{
			//then there must exist a corresponding navigation event
			some navEvent:NavigationEvent|{
				navEvent.origin = meta.origin
				navEvent.oldDoc = doc
			}
		}
    }   
}

//user cannot navigate?

fact Navigation{
	all ne:NavigationEvent|{
		some s:ParserState, meta: MetaElement|{
			ne.oldDoc = s.document
			meta in s.document.elements 
			meta.origin = ne.origin
		} /*or 
		some s:ParserState, scriptObj:ScriptObject|{
			scriptObj = ne.script
			scriptObj.element in s.document.elements 
		}*/
	}
}

run RunToEmpty{
	//last.tokenQueue.eleSeq.isEmpty
	some DomManipulationEvent
}for 5

run sanityCheck{
	some s:ParserState, s':s.next, ele:Element|{
		s'.next = last
		ele in s'.document.elements
		ele not in last.document.elements
		s.tokenQueue.eleSeq.first != s'.tokenQueue.eleSeq.first
	}
}for 5

fact no_meta_in_first{
	all meta:MetaElement|{
		meta not in univ.(first.tokenQueue.eleSeq)
	}
}

run injectMeta{
	// a meta element 
	some meta:MetaElement|{
		meta in last.document.elements
		meta not in first.document.elements
		meta not in univ.(first.tokenQueue.eleSeq)
	}
}for 10

run nav_works{/*
	some nav:NavigationEvent|{
		nav.origin.schema = JAVASCRIPT
	}*/

	some nav:NavigationEvent,doc:Document,script:ScriptObject, meta:MetaElement, s:ParserState|{
		meta in doc.elements
		meta.origin = nav.origin
		s.next = last
		script.element not in s.document.elements
		meta in s.document.elements
		script.element in last.document.elements
	}
}for 5

run innerHTMLCantInjectScripts{
	some scriptObj:ScriptObject |{
		last.tokenQueue.eleSeq[0].script = scriptObj and
		scriptObj.element not in univ.(first.tokenQueue.eleSeq)
	}
}for 5

run DominatrixssIsSecure{


}


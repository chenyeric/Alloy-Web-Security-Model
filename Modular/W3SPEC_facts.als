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
			ctxb in ctxa.children
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

//browser navigation policy
/*A browsing context A is allowed to navigate a second browsing context B if one of the following conditions is true:

1) Either the origin of the active document of A is the same as the origin of the active document of B, or
2) The browsing context A is a nested browsing context with a top-level browsing context, and its top-level browsing context is B, or
3) The browsing context B is an auxiliary browsing context and A is allowed to navigate B's opener browsing context, or
4) The browsing context B is not a top-level browsing context, but there exists an ancestor browsing context of B whose 
active document has the same origin as the active document of A (possibly in fact being A itself).*/
fact browsingContext_Navigation{
	all disj ctxA, ctxB:BrowsingContext|{
		ctxB in ctxA.canNavigate iff (
			ctxA.activeDocument.origin = ctxB.activeDocument.origin or // 1)
			(ctxA in ctxB.children and ctxB.isTop = TRUE) or //2
			(some ctxB.opener and ctxB.opener in ctxA.canNavigate) or //3
			some ctxC:BrowsingContext |{ //4
				ctxC in ctxB.ancestors
				ctxB.isTop = FALSE  
				ctxC.activeDocument.origin = ctxA.activeDocument.origin
			}
		)
	}
}

/*
Directly reachable browsing contexts are:
1)The browsing context itself.
2)All the browsing context's child browsing contexts.
3)The browsing context's parent browsing context.
4)All the browsing contexts that have the browsing context as their opener browsing context.
5)The browsing context's opener browsing context.
*/
fact browsingContext_directlyReachable{
	all ctx:BrowsingContext|{
		ctx.directlyReachable = (ctx + ctx.children + ctx.creator + ctx.opened)
	}
}

//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXX 5.1.5 Groupings of browsing contexts XXXXXXXXXXXXXXXXXXXXXXXXXXX
sig UnitOfRelatedBrowsingContext{
	browsingContexts: set BrowsingContext,
	unitOfsimilarOrigin: set UnitOfRelatedSimilarOriginBrowsingContext,
}

sig UnitOfRelatedSimilarOriginBrowsingContext{
	origin: one Origin,
	browsingContexts: set BrowsingContext,
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
	no unitctxa, unitctxb: UnitOfRelatedSimilarOriginBrowsingContext|{
		some ctx: BrowsingContext{
			ctx in unitctxa.browsingContexts and ctx in unitctxb.browsingContexts
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

/*TODO: Because they are nested through an element, child browsing contexts are always tied to a 
specific  Document in their parent browsing context. User agents must not allow the user to interact 
with child browsing contexts of elements that are in Documents that are not themselves fully active.*/


//-----------------------------------------CHECKS------------------------------------/

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
} for 5


//=================================ABSOLETE BELOW===================================//

/*
fact SOPEnforcementForCanAccess {
  all disj f1, f2: Frame | {
    some f2.dom.effectiveOrigin => { //case where f2 sets document.domain
       f1.enforcer !in FirefoxSOP => 
            f2 in f1.canAccess implies 
                 f1.dom.effectiveOrigin = f2.dom.effectiveOrigin
       f1.enforcer in FirefoxSOP => 
            f2 in f1.canAccess implies {
                 ( f1.dom.effectiveOrigin = f2.dom.effectiveOrigin) or 
                 ( f1.dom.defaultOrigin = f2.dom.effectiveOrigin ) or 
                 ( f1.dom.effectiveOrigin = f2.dom.defaultOrigin) or
                 ( f1.dom.defaultOrigin = f2.dom.defaultOrigin)
             }
    }
    no f2.dom.effectiveOrigin => { // case where f2 does not set document.origin
       f2 in f1.canAccess implies {
             (no f1.dom.effectiveOrigin) 
             ( f1.dom.defaultOrigin = f2.dom.defaultOrigin)
       }
    }

  }
}

pred canAccessChained [accessor:SOPObject, resource:SOPObject] {
   resource in accessor.*canAccess
}


check inLinescriptsAreSane{
	no s:scriptDOM | {
		INLINE in s.attribute
		s.srcOrigin!=s.embeddedOrigin
	}
}for 5

run completesanity {
  some o1:Frame | o1.enforcer = IE6SOP
}
for 3

run effectiveOriginSanityCheck {
  some disj o1, o2: Frame | {
         o1.enforcer = o2.enforcer
         o1.dom.defaultOrigin != o2.dom.defaultOrigin
         o2 in o1.*canAccess
  }
} for 3


run firefoxAccessThroughDefaultOrigin{
 some disj o1, o2: Frame | {
         o1.enforcer = Firefox4SOP
         o2.enforcer = Firefox4SOP
         o1.dom.effectiveOrigin != o2.dom.effectiveOrigin
         o2 in o1.*canAccess
  }

} for 3 but 1 NetworkEndpoint



run unauthorizedAccessForSpec {
  some disj vict, atk: Frame|  {
         vict.enforcer = specSOP
         atk.enforcer = specSOP
         vict.dom.defaultOrigin = vict.dom.effectiveOrigin // victim sets effective = default
         !isSubdomainOf[atk.dom.defaultOrigin.dnslabel, vict.dom.defaultOrigin.dnslabel] //Attacker is not subdomain of vict, which makes attack trivial
         canAccessChained[atk, vict]
  }
} for 8 but 1 NetworkEndpoint


run unauthorizedAccessForFirefox { //discovers the Firefox bug
  some disj vict, atk: Frame |  {
         vict.enforcer = Firefox4SOP
         atk.enforcer = Firefox4SOP
         no intermediate:Frame | {intermediate != vict and intermediate.dom.defaultOrigin = vict.dom.defaultOrigin}
         vict.dom.defaultOrigin = vict.dom.effectiveOrigin // victim sets effective = default
         !isSubdomainOf[atk.dom.defaultOrigin.dnslabel, vict.dom.defaultOrigin.dnslabel] //Attacker is not subdomain of vict, which makes attack trivial
         canAccessChained[atk, vict]
  }
} for 4 but 1 NetworkEndpoint


*/


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

run topNavigationCanHappen{
		some frm: IframeElement, ctx:BrowsingContext{
			ctx = frm.nestedContext.top
			ctx in frm.nestedContext.canNavigate
		}
} for 4

//-----------------------------CHECKS FOR IFRAME + SANDBOX------------------------/
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

//============================JAVASCRIPT ===========================/


//=====================Same Origin Policy
//User agents must raise a SECURITY_ERR exception whenever any 
//properties of a Document object are accessed by scripts whose effective 
//script origin is not the same as the Document's effective script origin.
fact SameOriginPolicy{
	all script: ScriptElement, obj:ScriptableObject|{
		some doc:scriptObj_Document|{
			obj in script.canAccess iff (
				obj in doc and
				doc.domObj.effectiveScriptOrigin = script.~elements.effectiveScriptOrigin
			)
		}
	}
}

//one to one relationship
fact script_BrowsingContext_relationship{
	all disj scriptctxa,scriptctxb:scriptObj_BrowsingContext|{
		one ctxa: BrowsingContext|{
			scriptctxa.domObj = ctxa
			scriptctxb.domObj != ctxa
		} 
	}
}

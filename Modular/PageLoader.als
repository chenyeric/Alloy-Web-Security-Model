
open DNSAndOrigin
open basicDeclarations
open HTMLElements
open DOM_API

enum Bool { TRUE, FALSE} //hack to get boolean
sig String{} //used in things like browsing context name

sig WindowProxy{} //the window object
sig History{} //history object

sig BrowsingContext {
	window: set WindowProxy, //the unique window object that scripts can access
	sessionHistory: one History, //the history object of this browsing context
    opener: lone BrowsingContext, //opener page
	opened: set BrowsingContext, // all the browsing contexts that was opened
	creator: lone BrowsingContext,

	name: lone String, //name of the browsing context

	isTop: one Bool, //is this the top browsing context?
	isFullyActive: one Bool, //is this browsing context fully active?

	activeDocument: one Document,
	creatorDocument: Document,
	documents: set Document, //set of all Documents
	
	//for nested browsing contexts
	parentDocument: lone Document,
	contextContainer: lone Element,
	parent: lone BrowsingContext,
	ancestors: set BrowsingContext,
	top: one BrowsingContext,

	//for nesting browsing contexts
	children: set BrowsingContext,

	//navigation
	canNavigate: set BrowsingContext,

	//grouping browsing context
	directlyReachable: set BrowsingContext,
}{

 /*In general, there is a 1-to-1 mapping from the Window object 
to the Document object. There are two exceptions. First, a Window can be reused 
for the presentation of a second Document in the same browsing context, such that the 
mapping is then 2-to-1. This occurs when a browsing context is navigated from the initial 
about:blank Document to another, with replacement enabled. Second, a Document can end up 
being reused for several Window objects when the document.open() method is used, such that the 
mapping is then 1-to-many.

A Document does not necessarily have a browsing context associated with it. In particular, 
data mining tools are likely to never instantiate browsing contexts.
*/
}


sig Document {

	browsingContext: one BrowsingContext, // which BC this document belongs to

	charset: one CHARACTEREncoding,
	type: one MIMEType,
	url: one URLType,
	origin: one Origin,
	effectiveScriptOrigin: lone Origin,	

	html: HTMLElement,
	elements: set Element,
}

//The origin of about_blank
/*
fact originOfAboutBlank{
	all doc: Document|{
		//doc.url = ABOUT_BLANK implies 

	}
}*/

enum CHARACTEREncoding{UTF8}
enum URLType{NORM, ABOUT_BLANK, DATA}
enum MIMEType{APPLICATION_JAVASCRIPT, APPLICATION_JSON, TEXT_HTML}



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
			pctx = ccctx.~nestedContext.~elements.~activeDocument
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


sig Element{} //html element

sig HTMLElement extends Element{
	head: HEADElement,
	body: BODYElement,
}

sig ScriptElement extends Element{
	canAccess: set ScriptableObject,
}

sig HEADElement extends Element{}
sig BODYElement extends Element{}
//iframe can nest other browsing contexts
sig IframeElement extends Element{
	nestedContext: BrowsingContext,
	sandboxPolicies: set iframe_sandbox_policy,
}

enum iframe_sandbox_policy {
	NOT_ALLOW_SAME_ORIGIN, 
	NOT_ALLOW_TOP_NAVIGATION, 
	NOT_ALLOW_FORMS, 
	NOT_ALLOW_SCRIPTS
}

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
		topctx.isTop = True
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
			ctx.activeDocument.effectiveOrigin != randomfrm.dom.effectiveOrigin  
			ctx.activeDocument.effectiveOrigin != randomfrm.dom.defaultOrigin
		}
	}
}for 7


check NestedAllowScriptPolicyWorks{
	all disj sandboxctx, ctx:BrowsingContext{
		{			
			sandboxctx in ctx.ancestors  //iframe sandbox sandboxes a frame
			NOT_ALLOW_SCRIPTS in most_strict_sandbox_policy[sandboxctx.contextContainer] //but the sandbox has scripts disabled
		}implies
			no (ctx.activeDocument.elements && ScriptElement) //then the frame must also have scripts disabled
	}
}for 7

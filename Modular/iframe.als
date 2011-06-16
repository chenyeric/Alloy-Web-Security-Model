//open basicDeclarations
open DNSAndOrigin
open SOPDeclarations
//open CSP



fact ParentChildRelation{
	all pfrm, cfrm:Frame |{
		cfrm in pfrm.childFrame implies 
			pfrm = cfrm.parentFrame
	}
}


//sig ChromeFrame extends Frame{} //frame navigation for chrome is a bit different

//let's assume that each browser has 1 rendering engine (the FF model)
//Window==>frames==>script contexts
sig Window {
	//inBrowser: one Browser,
    top: one Frame,
	contentFrames: set Frame
}{
   //top frame has no parent
  	no top.parentFrame

	//all contents are reachable from top frame
  	contentFrames=top.*childFrame

}


//all frames must be inside ONE and only ONE Window
fact OneWindowOneDomPerFrame{
	all frm:Frame|{					//every frame must have
		one win:Window|{ //one window
			frm = win.top or			//such that, the frame is either the top level frame or
			frm in win.top.*childFrame //it is a child frame 
		}
	}
}

// only top frame can be initiated by the user
fact UserInitiatedFrames{
	all frm:Frame|{
		no frm.initiator implies 
			no frm.parentFrame
	}
}

//frames can only initiate other frames that they are "allowed" to navigate
fact InitiationImpliesCanNavigate{
	all frm1, frm2:Frame|{
		frm1.initiator=frm2 implies 
			frm1 in frm2.canNavigate
	}
}

//frames cannot initiate(load) each other
fact NoBidirectionalLoad{
	no disj frm1,frm2:Frame|{
		frm1.initiator= frm2
		frm2.initiator= frm1
	}
}


//=============W3 spec navigation policy=============/
/*
A browsing context A is allowed to navigate a second browsing context B if one of the following conditions is true:

1) Either the origin of the active document of A is the same as the origin of the active document of B, or
2) The browsing context A is a nested browsing context with a top-level browsing context, and its top-level browsing context is B, or
3) The browsing context B is an auxiliary browsing context and A is allowed to navigate B's opener browsing context, or
4) The browsing context B is not a top-level browsing context, but there exists an ancestor browsing context of B whose active 
document has the same origin as the active document of A (possibly in fact being A itself).
*/
fact W3NavPolicy{
	all disj nav_frm, main_frm:Frame|{ 
		nav_frm in main_frm.canNavigate implies ( //main frame can navigate nav frame if:
			nav_frm.dom.effectiveOrigin = main_frm.dom.effectiveOrigin or //1) they are from the same origin or,
			some win:Window|{ //2) nav frm and main frm are in the same window and nav frm is the top frm
				(nav_frm + main_frm) in win.contentFrames
				nav_frm = win.top
			} or
			some win:Window|{ //3) nav is an auxilliary context and main is allowed to navigate nav's initiator
				nav_frm = win.top
				nav_frm.initiator in main_frm.canNavigate
			} or
			some win:Window{
				nav_frm != win.top //4) nav is not a top frame
				some p_nav_frm:Frame|{
					nav_frm = p_nav_frm.*childFrame //4) but there exists some ancestor of nav
					p_nav_frm.dom.effectiveOrigin= main_frm.dom.effectiveOrigin //4) who has the same origin as main 
				}

			}
		)
   }
}



//TODO: additional fact for chrome frame 


//---------------------------------------------IFRAME SANDBOX---------------------/

//define sandbox attributes
enum iframe_sandbox_policy {NOT_ALLOW_SAME_ORIGIN, NOT_ALLOW_TOP_NAVIGATION, NOT_ALLOW_FORMS, NOT_ALLOW_SCRIPTS}

//iframe sandbox
sig IframeSandbox extends Frame{
	policies: set iframe_sandbox_policy, //attributes for this sandbox
}

//the sandbox policies for a frame should be the most strict policy after combining its parents policy
fun most_strict_sandbox_policy[frm:Frame]:set iframe_sandbox_policy{
	frm.policies+frm.*parentFrame.policies //union of all the restrictions
}

fact IframeSandboxCannotBeTopLevelFrame{
	all sandbox:IframeSandbox, win:Window{
		sandbox != win.top // iframe sandbox cannot be the top level frame for ANY window
	}
}

//iframe sandbox navigation poicy
fact SandboxNavigationPolicy{

	//iframe sandbox can ONLY navigate its top frame if Allow navigation is set
	all disj sandboxfrm, frm:Frame, win:Window|{
		{
			//sandboxfrm in IframeSandbox     
			frm in sandboxfrm.canNavigate  //if sandbox can navigate a frame, then...
		} implies{
			(sandboxfrm+frm) in win.contentFrames //this frame must be in the same window as the sandbox and...
			frm = win.top //this frame must be the top level frame
		}
	}

	//if allow navigation is not set, then it shouldn't be able to navigate anything
	all disj sandboxfrm , topfrm:Frame , win:Window|{
		{
			//sandboxfrm in IframeSandbox
			(sandboxfrm+topfrm) in win.contentFrames
			topfrm = win.top
			NOT_ALLOW_TOP_NAVIGATION in most_strict_sandbox_policy[sandboxfrm]
		} implies //if allow navi attr is not set
			topfrm !in sandboxfrm.canNavigate //then top frame cannot be navigated by sandboxed frame
	}
}


fact SandboxOriginPolicy{
	//if allow same origin is not set, then the sandbox should have its unique origin
	all disj sandboxfrm, frm:Frame{
		{
			//sandboxfrm in IframeSandbox
			NOT_ALLOW_SAME_ORIGIN in most_strict_sandbox_policy[sandboxfrm] //if allow same origin is not set
		}implies{
			sandboxfrm.dom.effectiveOrigin = sandboxfrm.dom.defaultOrigin //sandbox cannot set its document.domain
			sandboxfrm.dom.effectiveOrigin != frm.dom.effectiveOrigin
			sandboxfrm.dom.effectiveOrigin != frm.dom.defaultOrigin    //sandbox must have its own unique origin
		}
	}
}


fact SandboxScriptPolicy{
	//if allow script is not set, then the sandbox should not have a script element
	all sandboxfrm:Frame{
		NOT_ALLOW_SCRIPTS in most_strict_sandbox_policy[sandboxfrm] implies
			no sandboxfrm.scripts
	}
}


//-----------------------------CHECKS FOR IFRAME + SANDBOX------------------------/

//there should be no loops
check NoLoopInParentChildFrame{
	no disj pfrm,cfrm:Frame, win:Window|{
		(pfrm+cfrm) in win.contentFrames
		pfrm in cfrm.^parentFrame
		cfrm in pfrm.^parentFrame
	}
}for 5


run FramesAreSane{
	some disj frm1, frm2:Frame{
		some win:Window{
			(frm1+frm2) in win.contentFrames
			frm1 = win.top
		}
	}
}for 2


run topNavigationCanHappen{
	some win:Window {
		some disj cfrm,tfrm: Frame{
			tfrm = win.top
			cfrm in tfrm.*childFrame
			cfrm = tfrm.initiator
		}
	}
} for 4

check CrossOriginNavigationForUnrelatedFramesShouldNotHappen{
	no disj nav_frm, main_frm:Frame| {
		nav_frm in main_frm.canNavigate // main frame can navigate nav frame
		some disj main_win, nav_win:Window|{
			nav_frm = nav_win.*contentFrames //nav frame is the top level frame
			main_frm = main_win.*contentFrames
		}
		nav_frm.initiator!=main_frm // the frames are not initiated by each other
		main_frm.initiator!=nav_frm
		nav_frm.dom.effectiveOrigin != main_frm.dom.effectiveOrigin // this is a cross origin navigation
	}
} for 5

//sandbox navigation policy checker
check NestedAllowNavigationWorks{
	no disj nestedfrm, sandboxfrm, topfrm, frm:Frame, win:Window|{
		sandboxfrm in IframeSandbox
		(sandboxfrm+topfrm+nestedfrm) in win.contentFrames //if the top frame of a window sandboxes another frame...
		topfrm = win.top
		nestedfrm in sandboxfrm.*childFrame //sandboxed frame has a childframe
		
		NOT_ALLOW_TOP_NAVIGATION in sandboxfrm.policies //policy exists to disallow top navigation

		//the nested, sandboxed frame should no tbe able to initiate another frame that navigates the top
		nestedfrm = frm.initiator

		//topfrm.dom.effectiveOrigin = frm.dom.effectiveOrigin
		topfrm in frm.canNavigate
		
	}
} for 5

check NestedAllowSameOriginWorks{
	all disj sandboxfrm, frm, randomfrm:Frame{
		{
			sandboxfrm in IframeSandbox 
			frm in sandboxfrm.*childFrame  //iframe sandbox sandboxes a frame
			NOT_ALLOW_SAME_ORIGIN in most_strict_sandbox_policy[sandboxfrm] //but the sandbox is putinto a unique origin
		}implies{ //then the embedded frame must also be in a unique origin
			frm.dom.effectiveOrigin != randomfrm.dom.effectiveOrigin  
			frm.dom.effectiveOrigin != randomfrm.dom.defaultOrigin
		}
	}
}for 7

check NestedAllowScriptPolicyWorks{
	all disj sandboxfrm, frm:Frame{
		{
			sandboxfrm in IframeSandbox 
			frm in sandboxfrm.*childFrame  //iframe sandbox sandboxes a frame
			NOT_ALLOW_SCRIPTS in most_strict_sandbox_policy[sandboxfrm] //but the sandbox has scripts disabled
		}implies
			no frm.scripts //then the frame must also have scripts disabled
	}
}for 7

/*
//===========absolete=============/
fun involvedServers[t:HTTPTransaction]:set NetworkEndpoint{
	( (t.*cause & HTTPTransaction).resp.from + getPrincipalFromOrigin[(transactions.t).owner].servers )
}

fun involvedContexts[t:HTTPTransaction]:set ScriptContext{
	transactions.(t.*cause  & HTTPTransaction) +transactions.t
}

fun involvedOrigins[t:HTTPTransaction]:set Origin{
  (t.*cause & HTTPTransaction).resp.host + (transactions.t).owner
}
*/

open basicDeclarations.als
open DNSAndOrigin.als
open SOPDeclarations.als

sig Frame {
	//context: one ScriptContext,
	initiator: Frame,
	dom: documentDOM
}

sig ChromeFrame extends Frame{} //frame navigation for chrome is a bit different

//let's assume that each browser has 1 rendering engine (the FF model)
//Window==>frames==>script contexts
sig Window {
	//inBrowser: one Browser,
    top: one Frame,
	contentFrames: set Frame,
	childFrames: Frame lone -> Frame,
	parentFrame: Frame -> lone Frame
}{
   //top frame has no parent
  	no top.parentFrame

	//all contents are reachable from top frame
  	contentFrames=top.*childFrames

	//parent is inverse of child
	parentFrame=~childFrames

}


//TODO: all script contexts must be inside a frame


//all frames must be inside ONE and only ONE Window
fact frames_are_sane{
	all frm:Frame|{					//every frame must have
		one win:Window|{ //one window
			frm = win.top or			//such that, the frame is either the top level frame or
			frm = top.*(win.childFrame) //it is a child frame 
		}
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
		nav_frm.dom in main_frm.dom.canNavigate implies ( //main frame can navigate nav frame if:
			nav_frm.dom.effectiveOrigin = main_frm.dom.effectiveOrigin or //1) they are from the same origin or,
			one win:Window|{ //2) nav frm and main frm are in the same window and nav frm is the top frm
				(nav_frm + main_frm) in win.contentFrames
				nav_frm = win.top
			} or
			one win:Window|{ //3) nav is an auxilliary context and main is allowed to navigate nav's initiator
				nav_frm = win.top
				nav_frm.initiator.dom in main_frm.dom.canNavigate
			} or
			one win:Window{
				nav_frm != win.top //4) nav is not a top frame
				some p_nav_frm:Frame|{
					nav_frm = p_nav_frm.*(win.childFrame) //4) but there exists some ancestor of nav
					p_nav_frm.dom.effectiveOrigin= main_frm.dom.effectiveOrigin //4) who has the same origin as main 
				}

			}
		)
   }
}

//TODO: additional fact for chrome frame 

run topNavigationCanHappen{
	some win:Window {
		some cfrm,tfrm: Frame{
			tfrm = win.top
			cfrm in tfrm.*(win.childFrames)
			cfrm = tfrm.initiator
		}
	}
} for 5


//define sandbox attributes
abstract sig iframe_sandbox_policy{}
sig NOT_ALLOW_SAME_ORIGIN, NOT_ALLOW_TOP_NAVIGATION, NOT_ALLOW_FORMS, NOT_ALLOW_SCRIPTS extends iframe_sandbox_policy()

//iframe sandbox
sig IframeSandbox extends Frame{
	policies: set iframe_sandbox_policy, //attributes for this sandbox
}

//the sandbox policies for a frame should be the most strict policy after combining its parents policy
fun most_strict_sandbox_policy[frm:Frame]:set iframe_sandbox_policy{
	frm.policies+frm.*(frm.(~contentFrames).parentFrame).policies //union of all the restrictions

}

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

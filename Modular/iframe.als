open declarations_cookie_update

sig Frame {
	context: one ScriptContext,
	req : HTTPRequest  //the request for frame content
}


//let's assume that each browser has 1 rendering engine (the FF model)
//browser process==>frames==>script contexts
sig BrowserProcess {
	inBrowser: one Browser,
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


//all frames must be inside ONE and only ONE BrowserProcess
fact frames_are_sane{
	all frm:Frame{					//every frame must have
		one bp:BrowserProcess{ //one browser process
			frm = bp.top or			//such that, the frame is either the top level frame or
			frm = top.*(bp.childFrame) //it is a child frame 
		}
	}
}

//frame navigation policy
fact descendantPolicy{
	all bp: BrowserProcess{ // for all browser process
			no pfrm, cfrm:Frame {  //the following relations should not hold. 
				(pfrm + cfrm) in bp.contentFrames //1)if pfrm and cfrm are inside this browser process
				pfrm != bp.top           //2)parent frame is not top frame
				pfrm=cfrm.*(bp.parentFrame)        //3) if pfrm is in cfrm's parent chain
				cfrm.context in involvedContexts[pfrm.req.(~req)]	//4) the script context of cfrm is in the causual chain of pfrm
           }
	}
}

run topNavigationCanHappen{
	some bp:BrowserProcess {
		some cfrm,tfrm: Frame{
			tfrm = bp.top
			cfrm in tfrm.*(bp.childFrames)
			cfrm.context in involvedContexts[tfrm.req.(~req)]
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

fun involvedServers[t:HTTPTransaction]:set NetworkEndpoint{
	( (t.*cause & HTTPTransaction).resp.from + getPrincipalFromOrigin[(transactions.t).owner].servers )
}

fun involvedContexts[t:HTTPTransaction]:set ScriptContext{
	transactions.(t.*cause  & HTTPTransaction) +transactions.t
}

fun involvedOrigins[t:HTTPTransaction]:set Origin{
  (t.*cause & HTTPTransaction).resp.host + (transactions.t).owner
}

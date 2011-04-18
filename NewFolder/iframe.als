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

//all script contexts must be inside a frame, except for the top level frame

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



fun involvedServers[t:HTTPTransaction]:set NetworkEndpoint{
( (t.*cause & HTTPTransaction).resp.from + getPrincipalFromOrigin[(transactions.t).owner].servers )
}

fun involvedContexts[t:HTTPTransaction]:set ScriptContext{
	transactions.(t.*cause  & HTTPTransaction) +transactions.t
}

fun involvedOrigins[t:HTTPTransaction]:set Origin{
  (t.*cause & HTTPTransaction).resp.host + (transactions.t).owner
}

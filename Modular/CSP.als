//open basicDeclarations
open DNSAndOrigin
open SOPDeclarations
open iframe

sig CSPFrame extends Frame {
	//CSP policies
	csp: lone CSPPolicies
}

sig CSPPolicies{
	allowScript: set scriptDOM,
	frameAncestor: set Origin,
	frameSrc:set Origin
}


//----------------------------------------CSP facts----------------------------//
//script policy for CSP, we are not modelling eval
fact CSPAllowScripts{
	all script:scriptDOM, frm:Frame{
		//no inline scripts
		some frm.csp and INLINE in script.attribute	implies
			script not in frm.csp.allowScript

		//ALL whitelisted scripts are SAFE
		some frm.csp and SANITIZED not in script.attribute implies
			script not in frm.csp.allowScript

		//only whitelisted scripts may execute
		some frm.csp and script not in frm.csp.allowScript implies 
			script not in frm.scripts


		//incorrect mime types may not execute
		{
			some frm.csp
			script.mimeType != APPLICATION_JAVASCRIPT
			script.mimeType != APPLICATION_JSON
		}implies
			script not in frm.scripts
		
	}
}

fact CSPFrameSource{
	all frm:Frame,origin:Origin{
		some frm.csp and origin not in frm.csp.frameSrc implies{ // if an origin is not in the frame src
			all cfrm:Frame|{ // then no frames from that origin may load
				cfrm in frm.childFrame //as a DIRECT child frame, but may load as an indirect childframe
				origin not in cfrm.dom.effectiveOrigin
			}
		}
	}
}

//other src directives are not that important (ie style src, object src etc) so we skip it for now

//TODO: model data URI

//frame ancester policy for CSP
fact CSPFrameAncestors{
	all frm:Frame, origin:Origin{

		//TODO: this model is not very "correct" because the attacker can still "request" frames, just not render them

		//if frame ancestor directory was defined and origin is not a part of its ancestors
		some frm.csp.frameAncestor and origin not in frm.csp.frameAncestor implies 
			origin not in frm.*parentFrame.dom.effectiveOrigin //then origin must not be this frame's ancestor			

			//TODO: MAKE SURE THIS IS VALID	
			//origin not in frm.*parentFrame.dom.defaultOrigin
	}
}


//-------------------------------------CSP checks------------------------//
check FrameNavigationIsImpossibleWithFrameSrcDirective{
	no pfrm, cfrm:CSPFrame, origin:Origin{
		some pfrm.csp
		origin = cfrm.dom.effectiveOrigin
		origin not in pfrm.csp.frameSrc //if child frame is NOT allowed by the framesrc directive
		pfrm = cfrm.parentFrame
	}
}for 5

check ClickJackIsImpossibleWithFrameAncestorDirective{
	no pfrm,cfrm:CSPFrame, origin:Origin{
		some cfrm.csp.frameAncestor
		origin = pfrm.dom.effectiveOrigin
		origin not in cfrm.csp.frameAncestor // if parent frame is not allowed by frame ancestor
		pfrm = cfrm.*parentFrame 
	}
}for 5

check NonWhiteListedScriptImpossibleWithAllowScriptDirective{
	no script:scriptDOM, frm:CSPFrame{
		some frm.csp
		script not in frm.csp.allowScript //script is not allowed
		script in frm.scripts
	}
}for 5

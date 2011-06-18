open DNSAndOrigin
open SOPDeclarations
open iframe
open CSP
open SOPAndNetworkConnector


//--------------------------------- XSS ATTACKER--------------------------/

fact BEEP{
	all frm:Frame,script:scriptDOM|{
		{
			BEEP in frm.attribute 
			script in frm.scripts
		}implies{
			SANITIZED in script.attribute
		}
	}
}

check XSSAttackCannotHappenInCSP{
	no frm:Frame, script:scriptDOM|{
		some frm.csp //replace this line with whatever policy
		script in frm.scripts

		//not SANITIZED gives the attacker the ability execute malicious scripts
		//INLINE gives the attacker the ability execute any whitelisted scripts at her will
		(SANITIZED not in script.attribute) or (INLINE in script.attribute)
	}
}for 4

check XSSAttackCannotHappenInBeep{
	no frm:Frame, script:scriptDOM|{
		BEEP in  frm.attribute //replace this line with whatever policy
		script in frm.scripts

		//not SANITIZED gives the attacker the ability execute malicious scripts
		//INLINE gives the attacker the ability execute any whitelisted scripts at her will
		(SANITIZED not in script.attribute) or (INLINE in script.attribute)
	}
}for 4

//------------------------------Active Attacker -----------------------------/

//a document is vulnerable to active attackers if:
//1) A script that is served by an Attacker's PRINCIPAL is inside the victim's dom
check ActiveAttackerCannotAccessHTTPSDOM{
	//-------Attack model: Assume the user will click through warnings-----/
	

	no frm:Frame | {
		HTTPS = frm.dom.effectiveOrigin.Schema //the document is served with HTTPS
		frm.dom.effectiveOrigin.dnslabel in GOOD.dnslabel // if the document belongs to a good principal
	
		some script:Script |{
			script in frm.scripts
			script.embeddedOrigin.dnslabel in ACTIVEATTACKER
		}

	}
}


















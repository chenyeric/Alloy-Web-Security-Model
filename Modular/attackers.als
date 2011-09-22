open DNSAndOrigin
//open SOPDeclarations
open iframe
//open CSP
open SOPAndNetworkConnector 



//--------------------------------- XSS ATTACKER--------------------------/
/*
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
*/
//------------------------------Active Attacker -----------------------------/
/*
fact UserWillNotClickThroughSecurityWarning{
	//-------User model: Assume the user will NOT click through warnings-----/
	all cert1,cert2:Certificate, fn:FrameOnNetwork|{
		{
			BADCA = cert1.ca
			GOODCA = cert2.ca 
		} implies (cert1+cert2) not in fn.context.transactions.cert
	}

}
*/

//Locked SOP
fact LockedSOP{

	//if 2 doms has 2 different certs, then they can't be the same origin
	all dom1, dom2:documentDOM|{
		{
			GOODCA= dom1.transaction.cert.ca
			BADCA = dom2.transaction.cert.ca
		}implies 
			dom1.effectiveOrigin != dom2.effectiveOrigin
	}
}

run LSOPBugTest{
	some frm:Frame|{
		HTTPS = frm.dom.effectiveOrigin.schema //the document is served with HTTPS
		frm.dom.effectiveOrigin.dnslabel in GOOD.dnslabels // if the document belongs to a good principal
		GOODCA = frm.dom.transaction.cert.ca
		
		some script:frm.scripts|{
				HTTPS = script.srcOrigin.schema
				//script.srcOrigin.dnslabel in ACTIVEATTACKER.dnslabels 
				BADCA = script.transaction.cert.ca
			}
	}

}

//a document is vulnerable to active attackers if:
//1) A script that is served by an Attacker's PRINCIPAL can access the victim's dom
check ActiveAttackerCannotAccessHTTPSDOM{

	no frm:Frame|{
			//------- victim ------/
			HTTPS = frm.dom.effectiveOrigin.schema //the document is served with HTTPS
			frm.dom.effectiveOrigin.dnslabel in GOOD.dnslabels // if the document belongs to a good principal
			GOODCA = frm.dom.transaction.cert.ca

			//the attacker "Can" access it
			some dummy_frame:Frame, script:dummy_frame.scripts|{
				frm in dummy_frame.canAccess 
				HTTPS = script.srcOrigin.schema
				//script.srcOrigin.dnslabel in ACTIVEATTACKER.dnslabels 
				BADCA = script.transaction.cert.ca
			}
	}
	

}for 6



















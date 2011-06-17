open DNSAndOrigin
open SOPDeclarations
open iframe
open CSP

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

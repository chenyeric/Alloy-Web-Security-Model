
open DNSAndOrigin

abstract sig SOPObject {
   enforcer : one SOPEnforcer,   //Which Browser is doing the enforcement? Need a place for variations
   canAccess : set SOPObject,
   canNavigate: set SOPObject,
   //More to come such as canRead, canWrite, canNavigate, etc
}{

}


fact accessOnlyThroughSameEnforcer { // if 2 objects are not in the same browser, they can't access each other
   all disj o1, o2: SOPObject | 
       o1 in o2.canAccess implies o1.enforcer = o2.enforcer
}


/*****Different SOP Enforcer Flavors *********/
abstract sig SOPEnforcer{}

abstract sig FirefoxSOP extends SOPEnforcer{}
lone sig Firefox2SOP extends FirefoxSOP{}
lone sig Firefox3SOP extends FirefoxSOP{}
lone sig Firefox4SOP extends FirefoxSOP{}

abstract sig IESOP extends SOPEnforcer{}
lone sig IE6SOP extends IESOP{}
lone sig IE7SOP extends IESOP{}
lone sig IE8SOP extends IESOP{}

lone sig SafariSOP extends SOPEnforcer{}
lone sig OperaSOP extends SOPEnforcer{}
lone sig ChromeSOP extends SOPEnforcer{}
lone sig AndroidSOP extends SOPEnforcer{}

lone sig specSOP extends SOPEnforcer{}



enum MIMEType{APPLICATION_JAVASCRIPT, APPLICATION_JSON, TEXT_HTML}


//--------------------------------FRAME----------------------------/
sig Frame extends SOPObject{
	initiator: lone Frame,
	dom : one documentDOM,
	scripts: set scriptDOM,
	parentFrame: lone Frame,
	childFrame: set Frame,
    mimeType:  one MIMEType,
}
{ 
    this in canNavigate
    this in canAccess
}




//bijection btw frame and dom
fact OneFramePerDom{
	no this_dom:documentDOM | no this_dom.~dom // onto
	dom in Frame one -> one documentDOM // one-to-one
}

//relationship between frame and script
fact OneFramePerScript {
    no s:scriptDOM | no s.~scripts //"onto", though scripts is not a function
    scripts in Frame one -> set scriptDOM //one-to-many
}


//abstract sig DOMObject extends SOPObject {}

//add other DOMObjects here, such as imgs, etc.

//script object
sig scriptDOM {
	srcOrigin: one Origin, //the source origin of the script
	embeddedOrigin: one Origin, // the origin that embedded this script
	attribute: set scriptAttribute,
    mimeType:  one MIMEType,
}{
	INLINE in attribute implies srcOrigin = embeddedOrigin //only way for inline scripts to happen
}

//varrious attrbutes for scripts, ie inline, sanitized, etc
enum scriptAttribute {INLINE}


fact scriptDocumentRelation {
  all s:scriptDOM, d: scripts.s.dom | {
      (some d.effectiveOrigin) => s.embeddedOrigin = d.effectiveOrigin
      (no d.effectiveOrigin) => s.embeddedOrigin = d.defaultOrigin
     
   }
}


sig documentDOM {
   defaultOrigin : one Origin ,
   effectiveOrigin : lone Origin  // the effective origin is from document.domain, which can also be unused.
}

fact effectiveOriginLimitations {
  all d:documentDOM | {
     some d.effectiveOrigin => {
       //d.defaultOrigin.port = d.effectiveOrigin.port
       d.defaultOrigin.schema = d.effectiveOrigin.schema
       isSubdomainOf[d.defaultOrigin.dnslabel, d.effectiveOrigin.dnslabel]
     }
  }
}


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




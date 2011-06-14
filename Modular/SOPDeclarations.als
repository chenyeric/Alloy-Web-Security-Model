//JHB 6-1-11

open DNSAndOrigin

abstract sig SOPObject {
   enforcer : one SOPEnforcer,   //Which Browser is doing the enforcement? Need a place for variations
   canAccess : set SOPObject,
   canNavigate: set SOPObject,
   mimeType:  one MIMEType,
   //More to come such as canRead, canWrite, canNavigate, etc
}{
  this in canAccess // Objects can access themselves
  this in canNavigate //Objects can navigate themselves
}

enum MIMEType{APPLICATION_JAVASCRIPT, APPLICATION_JSON, TEXT_HTML}

fact accessOnlyThroughSameEnforcer { // if 2 objects are not in the same browser, they can't access each other
   all disj o1, o2: SOPObject | 
       o1 in o2.canAccess implies o1.enforcer = o2.enforcer
}


/*****Different SOP Enforcer Flavors *********/
abstract sig SOPEnforcer{}

abstract sig FirefoxSOP extends SOPEnforcer{}
one sig Firefox2SOP extends FirefoxSOP{}
one sig Firefox3SOP extends FirefoxSOP{}
one sig Firefox4SOP extends FirefoxSOP{}

abstract sig IESOP extends SOPEnforcer{}
one sig IE6SOP extends IESOP{}
one sig IE7SOP extends IESOP{}

one sig SafariSOP extends SOPEnforcer{}
one sig OperaSOP extends SOPEnforcer{}
one sig ChromeSOP extends SOPEnforcer{}
one sig AndroidSOP extends SOPEnforcer{}

one sig specSOP extends SOPEnforcer{}

abstract sig DOMObject extends SOPObject {}

//add other DOMObjects here, such as imgs, etc.

//script object
sig scriptDOM extends DOMObject{
	srcOrigin: one Origin, //the source origin of the script
	embeddedOrigin: one Origin, // the origin that embedded this script
	attribute: set scriptAttribute
}{
	INLINE in attribute implies srcOrigin = embeddedOrigin //only way for inline scripts to happen
}

//varrious attrbutes for scripts, ie inline, sanitized, etc
enum scriptAttribute {INLINE}


//Modeling Mozilla document.domain
sig documentDOM extends DOMObject {
   defaultOrigin : one Origin ,
   effectiveOrigin : lone Origin  // the effective origin is from document.domain, which can also be not used.
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
  all disj o1, o2: documentDOM | {
    some o2.effectiveOrigin => { //case where o2 sets document.domain
       o1.enforcer !in FirefoxSOP => 
            o2 in o1.canAccess implies 
                 o1.effectiveOrigin = o2.effectiveOrigin
       o1.enforcer in FirefoxSOP => 
            o2 in o1.canAccess implies 
                 ( o1.effectiveOrigin = o2.effectiveOrigin or 
                   o1.defaultOrigin = o2.effectiveOrigin )
    }
    no o2.effectiveOrigin => { // case where o2 does not set document.origin
      o2 in o1.canAccess implies {(no o1.effectiveOrigin) and (o1.defaultOrigin = o2.defaultOrigin)}
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

run effectiveOriginSanityCheck {
  some disj o1, o2: documentDOM | {
         o1.enforcer = IE6SOP
         o2.enforcer = IE6SOP
         o1.defaultOrigin != o2.defaultOrigin
         o2 in o1.*canAccess
  }
} for 4 but 1 NetworkEndpoint, 0 scriptDOM

run firefoxAccessThroughDefaultOrigin{
 some disj o1, o2: documentDOM | {
         o1.enforcer = Firefox4SOP
         o2.enforcer = Firefox4SOP
         o1.effectiveOrigin != o2.effectiveOrigin
         o2 in o1.*canAccess
  }
} for 4 but 1 NetworkEndpoint, 0 scriptDOM


run unauthorizedAccessForSpec {
  some disj vict, atk: documentDOM |  {
         vict.enforcer = specSOP
         atk.enforcer = specSOP
         vict.defaultOrigin = vict.effectiveOrigin // victim sets effective = default
         !isSubdomainOf[atk.defaultOrigin.dnslabel, vict.defaultOrigin.dnslabel] //Attacker is not subdomain of vict, which makes attack trivial
         canAccessChained[atk, vict]
  }
} for 8 but 1 NetworkEndpoint, 0 scriptDOM

run unauthorizedAccessForFirefox { //discovers the Firefox bug
  some disj vict, atk: documentDOM |  {
         vict.enforcer = Firefox4SOP
         atk.enforcer = Firefox4SOP
         vict.defaultOrigin = vict.effectiveOrigin // victim sets effective = default
         !isSubdomainOf[atk.defaultOrigin.dnslabel, vict.defaultOrigin.dnslabel] //Attacker is not subdomain of vict, which makes attack trivial
         canAccessChained[atk, vict]
  }
} for 3 but 1 NetworkEndpoint, 0 scriptDOM




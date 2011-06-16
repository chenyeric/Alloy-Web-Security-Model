open HTTPHdrDecls
open DNSAndOrigin

/******** The headers for bootstrapping CSP ******************/
/******** The alternate method of boostrapping is <META>.  This is as of yet not modeled *********/

sig XContentSecurityPolicyHeader extends HTTPResponseHeader {
    policy : set CSPDirective  // each policy is a set of directives
}

abstract sig CSPDirective {
   sourceList : set SourceExp + DirectiveKeywords
}

enum DirectiveKeywords {NONE_CSP, SELF_CSP, UNSAFE_INLINE_CSP, UNSAFE_EVAL_CSP} 

fact usageRestrictionUnsafeInline {
   all c:CSPDirective | UNSAFE_INLINE_CSP in c.sourceList implies ( c in script_src_Directive or
																							     c in style_src_Directive)
}

fact usageRestrictionUnsafeEval {
   all c:CSPDirective | UNSAFE_EVAL_CSP in c.sourceList implies c in script_src_Directive
}

sig SourceExp {
   scheme : lone Schema, // can be left empty
   host : lone DNSWildCard // can also be left empty, (but one of scheme and host must exist
   //lone port : Port
}

fact properSourceExp {
  no s:SourceExp | no s.scheme and no s.host
}

sig default_src_Directive extends CSPDirective{}
sig script_src_Directive extends CSPDirective{}
sig object_src_Directive extends CSPDirective{}
sig img_src_Directive extends CSPDirective{}
sig media_src_Directive extends CSPDirective{}
sig style_src_Directive extends CSPDirective{}
sig frame_src_Directive extends CSPDirective{}
sig font_src_Directive extends CSPDirective{}
sig xhr_src_Directive extends CSPDirective{}
sig frame_ancestors_Directive extends CSPDirective{}

run {
  some a:DirectiveKeywords | a= UNSAFE_INLINE_CSP
} for 2

//NOT modeling the report-uri, policy-uri, and options directives at the moment

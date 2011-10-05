open DNSAndOrigin
open basicDeclarations


enum Bool { TRUE, FALSE} //hack to get boolean
sig string{} //used in things like browsing context name


//================================Page Loader==============================/
sig WindowProxy{} //the window object
sig History{} //history object

sig BrowsingContext {
	window: set WindowProxy, //the unique window object that scripts can access
	sessionHistory: one History, //the history object of this browsing context
    opener: lone BrowsingContext, //opener page
	opened: set BrowsingContext, // all the browsing contexts that was opened
	creator: lone BrowsingContext,

	name: lone string, //name of the browsing context

	isTop: one Bool, //is this the top browsing context?
	isFullyActive: one Bool, //is this browsing context fully active?

	activeDocument: one Document,
	creatorDocument: Document,
	documents: set Document, //set of all Documents
	
	//for nested browsing contexts
	parentDocument: lone Document,
	contextContainer: lone Element,
	parent: lone BrowsingContext,
	ancestors: set BrowsingContext,
	top: one BrowsingContext,

	//for nesting browsing contexts
	children: set BrowsingContext,

	//navigation
	canNavigate: set BrowsingContext,

	//grouping browsing context
	directlyReachable: set BrowsingContext,
}{

 /*In general, there is a 1-to-1 mapping from the Window object 
to the Document object. There are two exceptions. First, a Window can be reused 
for the presentation of a second Document in the same browsing context, such that the 
mapping is then 2-to-1. This occurs when a browsing context is navigated from the initial 
about:blank Document to another, with replacement enabled. Second, a Document can end up 
being reused for several Window objects when the document.open() method is used, such that the 
mapping is then 1-to-many.

A Document does not necessarily have a browsing context associated with it. In particular, 
data mining tools are likely to never instantiate browsing contexts.
*/
}

//================================HTML ELEMENTS===========================/

sig Document {

	browsingContext: one BrowsingContext, // which BC this document belongs to

	charset: one CHARACTEREncoding,
	type: one MIMEType,
	url: one URLType,
	origin: one Origin,
	effectiveScriptOrigin: lone Origin,	

	html: HTMLElement,
	elements: set Element,
}

//The origin of about_blank
/*
fact originOfAboutBlank{
	all doc: Document|{
		//doc.url = ABOUT_BLANK implies 

	}
}*/

enum CHARACTEREncoding{UTF8}
enum URLType{NORM, ABOUT_BLANK, DATA}
enum MIMEType{APPLICATION_JAVASCRIPT, APPLICATION_JSON, TEXT_HTML}


sig Element{} //html element

sig HTMLElement extends Element{
	head: HEADElement,
	body: BODYElement,
}

sig HEADElement extends Element{}
sig BODYElement extends Element{}
//iframe can nest other browsing contexts
sig IframeElement extends Element{
	nestedContext: BrowsingContext,
	sandboxPolicies: set iframe_sandbox_policy,
}

enum iframe_sandbox_policy {
	NOT_ALLOW_SAME_ORIGIN, 
	NOT_ALLOW_TOP_NAVIGATION, 
	NOT_ALLOW_FORMS, 
	NOT_ALLOW_SCRIPTS
}


//================================SCRIPTS==============================/
sig ScriptElement extends Element{
	canAccess: set ScriptableObject,
}

sig ScriptableObject{} //all elements that can be accessed by script

sig scriptObj_BrowsingContext extends ScriptableObject{
	domObj: BrowsingContext,

	//section 5.1.6
	func_form_target: BrowsingContext,
	func_open: BrowsingContext,
	func_self: BrowsingContext,
	func_blank: BrowsingContext,
	func_parent: BrowsingContext,
	func_top: BrowsingContext
}

/* 
 ======> http://dvcs.w3.org/hg/domcore/raw-file/tip/Overview.html#interface-document
 
	readonly attribute DOMString URL;
  readonly attribute DOMString documentURI;
  readonly attribute DOMString compatMode;

           attribute DOMString charset;
  readonly attribute DOMString characterSet;
  readonly attribute DOMString defaultCharset;
  readonly attribute DOMString contentType;

  readonly attribute DocumentType? doctype;
  readonly attribute Element? documentElement;*/
sig scriptObj_Document extends ScriptableObject{	
	domObj: Document,
	domCharset: CHARACTEREncoding,
	domType: scriptObj_MIMEType,
	domUrl: scriptObj_URL,
	domElement: scriptObj_Element,
}

sig scriptObj_CHARACTEREncoding extends ScriptableObject{
	domObj: CHARACTEREncoding,
}

sig scriptObj_URL extends ScriptableObject{
	domObj: URLType
}

sig scriptObj_MIMEType extends ScriptableObject{
	domObj: MIMEType
}

sig scriptObj_Element extends ScriptableObject{
	domObj: Element
}



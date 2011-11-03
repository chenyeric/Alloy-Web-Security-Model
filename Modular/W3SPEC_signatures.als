open DNSAndOrigin
//open basicDeclarations


enum Bool { TRUE, FALSE} //hack to get boolean
enum HTMLtag {html,body, head, iframe, script} 
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
	contextContainer: lone IframeElement,
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

//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXX 5.1.5 Groupings of browsing contexts XXXXXXXXXXXXXXXXXXXXXXXXXXX
sig UnitOfRelatedBrowsingContext{
	browsingContexts: set BrowsingContext,
	unitOfsimilarOrigin: set UnitOfRelatedSimilarOriginBrowsingContext,
}

sig UnitOfRelatedSimilarOriginBrowsingContext{
	origin: one Origin,
	browsingContexts: set BrowsingContext,
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

//html element
sig Element{
	cause: lone DomManipulationEvent, // how is this element created?
	host: lone Document,
	tag: HTMLtag   //this element MUST exist for every element
} 

sig HTMLElement extends Element{
	head: HEADElement,
	body: BODYElement,
}{
	tag = html
}

sig HEADElement extends Element{}{
	tag = head
}

sig BODYElement extends Element{}{
	tag = body
}

//iframe can nest other browsing contexts
sig IframeElement extends Element{
	nestedContext: BrowsingContext,
	sandboxPolicies: set iframe_sandbox_policy,
	is_seamless: Bool
}{
	tag = iframe
}

enum iframe_sandbox_policy {
	NOT_ALLOW_SAME_ORIGIN, 
	NOT_ALLOW_TOP_NAVIGATION, 
	NOT_ALLOW_FORMS, 
	NOT_ALLOW_SCRIPTS
}

//================================Dom Events==========================/
sig DomEvent{}

//================================SCRIPTS==============================/
//HTML script tag
sig ScriptElement extends Element{
	script: ScriptObject
}{
	tag = script
}

//the actual script
sig ScriptObject{
	element: ScriptElement, //link scripts with their html element
	browsingContext: BrowsingContext,
	//section 5.1.6
	func_form_target: BrowsingContext,
	func_open: lone BrowsingContext,
	func_self: BrowsingContext,
	func_blank: lone BrowsingContext,
	func_parent: BrowsingContext,
	func_top: BrowsingContext
} 

sig DomManipulationEvent extends DomEvent{
	oldElement: lone Element,
	newElement: lone Element,
	script: ScriptObject
}





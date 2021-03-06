//Set up ordered status
open util/ordering[ParserState]
open DNSAndOrigin
//open basicDeclarations


enum Bool { TRUE, FALSE} //hack to get boolean
//Yuan add meta tag
enum HTMLtag {html,body, head, iframe, script, meta} 
//sig string{} //used in things like browsing context name


//================================Page Loader==============================/
sig WindowProxy extends Window{} //the window object
sig History{
	docs: set Document,
} //history object

sig Window{
	browsingContext: BrowsingContext
}

sig BrowsingContext {
	window: WindowProxy, //the unique window object that scripts can access
	sessionHistory: one History, //the history object of this browsing context
    opener: lone BrowsingContext, //opener page
	opened: set BrowsingContext, // all the browsing contexts that was opened
	creator: lone BrowsingContext,

	//name: lone string, //name of the browsing context

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
sig Location {
	href: Origin,
}

sig Document {

//	browsingContext: one BrowsingContext, // which BC this document belongs to

//	charset: one CHARACTEREncoding,
//	type: one MIMEType,
//	location: Location,
	origin: one Origin,
	effectiveScriptOrigin: one Origin,	

	root: HTMLElement,
	elements: set Element,
    
}

//The origin of about_blank
/*
fact originOfAboutBlank{
	all doc: Document|{
		//doc.url = ABOUT_BLANK implies 

	}
}*/
/*
enum CHARACTEREncoding{UTF8}
enum MIMEType{APPLICATION_JAVASCRIPT, APPLICATION_JSON, TEXT_HTML}
*/
//html element
sig Element{
	cause: lone DomManipulationEvent, // how is this element created?
	host: set Document, // the set is used to represent "time"
	hostEffectiveOrigin: Origin, //TODO: I need this to represent the "origin" of our host document
	tag: HTMLtag ,  //this element MUST exist for every element
    children: set Element

} 

sig HTMLElement extends Element{
	head: HEADElement,
//	body: BODYElement,
}{
	tag = html
}

enum HTTPEquivTypes{REFRESH}
sig MetaElement extends Element{
     origin : lone Origin,
	 http_equiv: one HTTPEquivTypes
}{
	tag = meta
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
//http://www.w3.org/TR/html5/scripting-1.html#scripting-1

//HTML script tag
sig ScriptElement extends Element{
	script: ScriptObject,
	async: one Bool,
	defer: one Bool,
	//src: lone string,
//add parserinserted flag yuan
     parserinserted: one Bool,
     forceasync : one Bool,
     executed : one Bool
}{
	tag = script
}


//the actual script
sig ScriptObject{
	element: ScriptElement, //link scripts with their html element
//	browsingContext: BrowsingContext,
	//section 5.1.6
/*
	func_form_target: BrowsingContext,
	func_open: lone BrowsingContext,
	func_self: BrowsingContext,
	func_blank: lone BrowsingContext,
	func_parent: BrowsingContext,
	func_top: BrowsingContext,
  */
} 





// methods that can be used to manipulate the dom
enum domManipulationAPI{
	//http://www.w3.org/TR/REC-DOM-Level-1/level-one-core.html
//	appendChild,
//	insertBefore,
//	replaceChild,

	//3.4 dynamic markup insersion
	//http://www.w3.org/TR/html5/dom.html#dynamic-markup-insertion
	document_write,

     //Yuan innerhtml
     innerhtml
 
}

sig DomManipulationEvent extends DomEvent{
	oldElement: lone Element,
	newElement: lone Element,
	script: ScriptObject,
	method: domManipulationAPI
}

sig NavigationEvent extends DomEvent{
	oldDoc: Document,
	newDoc: Document,
	origin: Origin, //the url this event is trying to navigate to.
	script: lone ScriptObject
}
/*
sig postMessageEvent extends DomEvent{
	source: Window,
	destination: Window,
	script: ScriptObject,
	origin: lone Origin
}
*/
//6.1 eventloop
// Instead of modeling the tokenizer, we are using a queue of tokens emitted by the tokenizer
sig TokenQueue{
	eleSeq: seq Element,
}

sig ParserState{
	tokenQueue:  TokenQueue,
	document:  Document
}


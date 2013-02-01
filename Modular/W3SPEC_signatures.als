open DNSAndOrigin
//open basicDeclarations


enum Bool { TRUE, FALSE} //hack to get boolean
enum HTMLtag {html,body, head, iframe, script} 
sig string{} //used in things like browsing context name


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
sig Location {
	href: Origin,
}

sig Document {

	browsingContext: one BrowsingContext, // which BC this document belongs to

	charset: one CHARACTEREncoding,
	type: one MIMEType,
	url: one URLType,
	location: Location,
	origin: one Origin,
	effectiveScriptOrigin: one Origin,	

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
//yuan:add flag for executed or not?
     executed: one Bool

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
//http://www.w3.org/TR/html5/scripting-1.html#scripting-1

//HTML script tag
sig ScriptElement extends Element{
	script: ScriptObject,
	async: one Bool,
	defer: one Bool,
	src: lone string,
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
	browsingContext: BrowsingContext,
	//section 5.1.6
	func_form_target: BrowsingContext,
	func_open: lone BrowsingContext,
	func_self: BrowsingContext,
	func_blank: lone BrowsingContext,
	func_parent: BrowsingContext,
	func_top: BrowsingContext
} 

// 6.1.4 Event loops - http://www.w3.org/html/wg/drafts/html/master/webappapis.html#event-loop
//sig EventLoop{
//	unitOfRelatedSimilarOriginBrowsingContext: lone //UnitOfRelatedSimilarOriginBrowsingContext,

//}{
	//An event loop always has at least one browsing context.
//	some //unitOfRelatedSimilarOriginBrowsingContext.browsingContexts
//}



// methods that can be used to manipulate the dom
enum domManipulationAPI{
	//http://www.w3.org/TR/REC-DOM-Level-1/level-one-core.html
	appendChild,
	insertBefore,
	replaceChild,

	//3.4 dynamic markup insersion
	//http://www.w3.org/TR/html5/dom.html#dynamic-markup-insertion
	document_write,

	//6.1.5 javascript: url scheme
	//http://www.w3.org/html/wg/drafts/html/master/webappapis.html#javascript-protocol
	javascriptUrl
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
	script: lone ScriptObject
}

sig postMessageEvent extends DomEvent{
	source: Window,
	destination: Window,
	script: ScriptObject,
	origin: lone Origin
}

//6.1 eventloop
enum Task {
                     Event,
                     Callback,
                     Parsing,
                     Resource,
                     Element // similar to element, how to combine two sigs?
}

sig State { 
      setdocwrite: one Bool, 
      setdomcontentloaded: one Bool,                            
      seteventlope: one Bool,
      setbrowsingcontext: one Bool
}

sig EventLoop {
               taskqueues : lone TaskQueue
               unitOfRelatedSimilarOriginBrowsingContext: lone UnitOfRelatedSimilarOriginBrowsingContext//at most one browsingcontext for one eventloop
	          browseringcontexts: some unitOfRelatedSimilarOriginBrowsingContext.browsingContexts //An event loop always has at least one browsing context.
               domcontentloaded : one bool

}
sig TaskQueue{
          taskseq :  seq Task  // squence of taskqueues, can be   Events, Callbacks, Parsing etc.                     
}

//listofscripts
sig listscriptexecutefinishparse{
    list : seq ScriptElement
}

sig listscriptpendingparseblock{
    list : seq ScriptElement
}

sig listscriptinorder{
    list : seq ScriptElement

}

sig listscriptsoon{
    list : seq ScriptElement

}

//Set up ordered status
open util/ordering[State] as State
open util/ordering[eventloop] as EventState
/*
sig State { 
      setdocwrite: one Bool, 
      setdoncontentloaded: one Bool,                            
      seteventlope: one Bool,
      setbrowsingcontext: one Bool
}
*/
sig EventSate {
   eventloop : one EventLoop
}


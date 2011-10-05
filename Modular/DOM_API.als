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
sig scriptObj_Document{	
	domObj: Document,
	_charset: CHARACTEREncoding,
	_type: scriptObj_MIMEType,
	_url: scriptObj_URL,
	_element: scriptObj_Element,
}

sig scriptObj_CHARACTEREncoding extends ScriptObject{
	domObj: CHARACTEREncoding,
}

sig scriptObj_URL extends ScriptObject{
	domObj: URLType
}

sig scriptObj_MIMEType extends ScriptObject{
	domObj: MIMEType
}

sig scriptObj_Element extends ScriptObject{
	domObj: Element
}


//=====================Same Origin Policy
//User agents must raise a SECURITY_ERR exception whenever any 
//properties of a Document object are accessed by scripts whose effective 
//script origin is not the same as the Document's effective script origin.
fact SameOriginPolicy{
	all script: ScriptElement, obj:ScriptObject|{
		some doc:scriptObj_Document|{
			obj in script.canAccess iff (
				obj in doc and
				doc.domObj.effectiveScriptOrigin = script.~elements.effectiveScriptOrigin
			)
		}
	}
}

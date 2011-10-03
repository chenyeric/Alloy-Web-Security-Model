open PageLoader

sig ScriptableObject{} //all elements that can be accessed by script


sig scriptObj_BrowsingContext extends ScriptableObject{
	domObj: BrowsingContext,

	//section 5.1.6
	_form_target: BrowsingContext,
	_open: BrowsingContext,
	_top: BrowsingContext,
	_self: BrowsingContext,
	_blank: BrowsingContext,
	_parent: BrowsingContext,
	_top: BrowsingContext
}

//one to one relationship
fact script_BrowsingContext_relationship{
	all disj scriptctxa,scriptctxb:scriptObj_BrowsingContext|{
		one ctxa: BrowsingContext|{
			scriptctxa.domObj = ctxa
			sctiptctxb.domObj != ctxa
		} 
	}
}



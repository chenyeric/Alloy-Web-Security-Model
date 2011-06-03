open basicDeclarations

/************************************
* CSRF
*
************************************/


// RFC talks about having Origin Chain and not a single Origin
// We handle Origin chain by having multiple Origin Headers 
sig OriginHeader extends HTTPRequestHeader {theorigin: Origin}


fun getFinalResponse[request:HTTPRequest]:HTTPResponse{
        {response : HTTPResponse | not ( response.statusCode in RedirectionStatus) and response in ((req.request).*(~cause)).resp}
}

pred isFinalResponseOf[request:HTTPRequest, response : HTTPResponse] {
       not ( response.statusCode in RedirectionStatus)
       response in ((req.request).*(~cause)).resp
}


lone sig ORIGINAWARE extends NormalPrincipal{}


fact CSRFProtection {
	all aResp:HTTPResponse | aResp.from in ORIGINAWARE.servers and aResp.statusCode=c200 implies {
		(resp.aResp).req.method in safeMethods or (
		let theoriginchain = ((resp.aResp).req.headers & OriginHeader).theorigin |
			some theoriginchain and theoriginchain.dnslabel in ORIGINAWARE.dnslabels
		)
	}
}



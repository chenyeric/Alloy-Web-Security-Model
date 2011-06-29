open SOPAndNetworkConnector as s


sig FrameWithXHR extends FrameOnNetwork {
      canSendXHRTo: set Origin,
      canReadXHRFrom: set Origin,
}

fact XHREnforcement {
     all f: FrameWithXHR, o:Origin | {
        o in f.canSendXHRTo => f.dom.defaultOrigin = o
        o in f.canReadXHRFrom => f.dom.defaultOrigin = o
     }
}

fact XHRTransactionsObeySOP {
    all f: FrameWithXHR, t: f.context.transactions | {
         t.cause in (XMLHTTPRequest+HTTPTransaction) =>{ t.req.host in f.canSendXHRTo 
                                                                                       t.resp.host in f.canReadXHRFrom}
         ((t.cause in HTTPTransaction) and 
          (t.cause.*cause in (XMLHTTPRequest+HTTPTransaction)) ) =>
                                                                                     { t.req.host in f.canSendXHRTo 
                                                                                       t.resp.host in f.canReadXHRFrom}
    }
}
    
run XHRSanity {
   some f: FrameWithXHR, o: Origin | o in f.canSendXHRTo and o in f.canReadXHRFrom
} for 3


run XHRSanity2{
   some f: FrameWithXHR, t: f.context.transactions, o: f.canSendXHRTo | t.req.host = o
} for 6

open SOPDeclarations as s

sig FrameWithXHR extends Frame {
      canSendXHRTo: set Frame,
      canReadXHRFrom: set Frame 
}

fact XHREnforcement {
     all disj f1, f2: FrameWithXHR | {
        f2 in f1.canSendXHRTo => f1.dom.defaultOrigin = f2.dom.defaultOrigin
        f2 in f1.canReadXHRFrom => f1.dom.defaultOrigin = f2.dom.defaultOrigin
     }
}
    
run XHRSanity {
   some disj f1, f2: FrameWithXHR | f2 in f1.canSendXHRTo and f2 in f1.canReadXHRFrom
} for 3

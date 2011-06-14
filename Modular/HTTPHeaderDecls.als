
abstract sig Method {}
one sig GET extends Method {}
one sig PUT  extends Method {}
one sig POST extends Method {}
one sig DELETE extends Method {}
one sig OPTIONS extends Method {}

fun safeMethods[]:set Method {
	GET+OPTIONS
}

abstract sig HTTPHeader {}	
abstract sig HTTPResponseHeader extends HTTPHeader{} 
abstract sig HTTPRequestHeader extends HTTPHeader{}

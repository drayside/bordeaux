 sig A { a:Int}

//abstract sig B extends A{}

inst i{
	2 sparse Int,
	A include s+d moreover e+r//,
	
	//a=s->-7+d->67	
}
{some s:A | s in A}

pred p{


}

run p for i

/*open util/integer
pred show {}

abstract sig c1_IMeasurable
{  }

sig c4_AbstractElement //extends c1_IMeasurable
{}

sig c10_AbstractSort //extends c1_IMeasurable
{}


inst configureproduct {
	2,
	c10_AbstractSort in IM_AbstractSort,
	c4_AbstractElement in IM_AbstractElement
}


run  show for configureproduct

*/
/*open util/integer
pred show {}

abstract sig A{  }

abstract sig D extends A {}

sig B extends D
{}

sig C extends A
{}

sig F {}
//sig D //extends A
//{}

inst configureproduct {
	3,
	//exactly 5 F,
	B include b+s,
	C include c
}


run  show for configureproduct
*/

/*sig A{
	b:Int}{}

pred p[]{
	some a:A | a.b =8
}

inst i{
6 Int,
A in a,
b include a->21} 

run p*/
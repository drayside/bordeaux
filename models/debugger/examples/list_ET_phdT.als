sig List{
	equivTo:set List,
	prefixes: set List
}
sig Thing{}

sig Nil extends List{}
sig Cons extends List{
	car: one Thing,
	cdr: one List
}

fact{
	all a:List | some e: Nil | e in a.^cdr
	all a,b: List | (a in b.equivTo) iff (a.car=b.car and a.cdr.equivTo = b.cdr.equivTo)
	all e:Nil, a:List| e in a.prefixes
	all e:Nil, a:Cons | not(a in e.prefixes)
	all a,b: Cons | (a in b.prefixes) iff (a.car=b.car and a.cdr in b.cdr.prefixes)
}

check {all a,b:List| (a in b.prefixes and b in a.prefixes) iff a in b.equivTo}




/**
* This model is created for elaborating the mutation idea.
**/

sig Node{
	nxt: set Node,
	val: set Int
}

pred noLoop{
	all n: Node| !(n in n.^nxt)
}
pred structuralConstraintNxt{
	all n: Node| one n.nxt
}

pred structuralConstraintVal{
	all n: Node| one n.val
}

pred lowerBound{
some Node 
}

pred sorted{
	all n:Node | some n.nxt implies gt[ n.nxt.val, n.val]
}

pred rootIsLowest{
	one n: Node |all n': Node-n | gt[n'.val, n.val]
}

check {
(noLoop and 
structuralConstraintNxt and
structuralConstraintVal and
lowerBound and
sorted
) implies rootIsLowest}

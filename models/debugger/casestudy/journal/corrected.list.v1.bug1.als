/**
* This model is created for elaborating the mutation idea.
**/

sig Node{
	nxt:  set  Node,
	val: Int}

pred noLoop{all n: Node| !(n in n.^nxt)}
pred structuralConstraint{all n: Node| lone n.nxt}
pred lowerBound{some Node}

pred sorted{
	all n:Node | some n.nxt implies gt[ n.nxt.val, n.val]
}

pred rootIsLowest{
	one n: Node |all n': Node-n | gt[n'.val, n.val]
}

check {
(noLoop and 
structuralConstraint and
lowerBound and
sorted
) implies rootIsLowest}

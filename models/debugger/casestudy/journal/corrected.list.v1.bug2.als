/**
* This model is created for elaborating the mutation idea.
**/

sig Node{
	nxt: set  Node,
	val: set Int}

pred noLoop{all n: Node| !(n in n.^nxt)}
pred structuralConstraintNxtFixed{
	all n: Node| lone n.nxt
}

pred structuralConstraintVal{
	all n: Node| one n.val
}
pred lowerBound{some Node}

pred allreachable{
	one n: Node | n.^nxt + n = Node
}

pred sorted{
	all n:Node | some n.nxt implies gt[ n.nxt.val, n.val]
}

pred rootIsLowest{
	one n: Node |all n': Node-n | gt[n'.val, n.val]
}

check {
(noLoop and 
structuralConstraintNxtFixed and
structuralConstraintVal and
lowerBound and
allreachable and
sorted
) implies rootIsLowest}

/**
* This model is created for elaborating the mutation idea.
**/

sig Node{
	left:  set  Node,
	right: set  Node}

pred acyclic{
	all n: Node| !( n in n.^(right + left) )
}

pred distinctChildren{
	all n: Node| /*!(no left && no right) implies*/ n.right != n.left
}

pred structuralConstraint{
	all n:Node | lone n.left
	all n:Node | lone n.right
}

pred lowerBoud{
	some Node
	// it also could be nxt. I.e `some nxt'
}

pred genBinaryTree{
	structuralConstraint
	acyclic
	distinctChildren
	lowerBoud
}

pred allReachable{
 some Node implies (	some n: Node| Node = n.*(left+right))
}

check {
{
	structuralConstraint
	acyclic
	distinctChildren
	lowerBoud
} implies allReachable }for 3

/*run{
	structuralConstraint
	acyclic
	distinctChildren
	lowerBoud
}*/

/*check {
some Node implies ( distinctChildren implies left != right  )
}

run {
not distinctChildren and acyclic}*/

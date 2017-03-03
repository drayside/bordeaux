sig Node{
	left:  lone  Node,
	right: lone  Node}

/**
*	Binary tree valid predicates
**/
pred isAcyclic[ n: set Node, right: Node->Node, left: Node->Node ]{
  all n': n| !( n' in n'.^(right + left) )
}

pred isValidNoCommon[ n: set Node, right: Node->Node, left: Node->Node ]{
  all n': n| ( some n'.left or some n'.right ) implies ( n'.left != n'.right )
}

pred singleParent[nodes: set Node, right: Node->Node, left: Node->Node] {
	all n: nodes | lone n.~(left + right)
}

pred rootedOne[ n: set Node, right: Node->Node, left: Node->Node ]{
	some n implies (one n': n| n = n'.*(right + left))
}

pred notAcyclic[ n: set Node, right: Node->Node, left: Node->Node ]{
  some n': n|  n' in n'.^(right + left) 
}

pred notInvalidNoCommon[ n: set Node, right: Node->Node, left: Node->Node ]{
  some n': n| ( n'.left = n'.right )
}
pred notValidNoCommon[ n: set Node, right: Node->Node, left: Node->Node ]{
  some n': n| ( some n'.left or some n'.right ) and ( n'.left = n'.right )
}


pred threeNodes[n: Node]{
	some disj n1,n2,n3: n | {n1+n2+n3} in Node
}

pred isTreeInstance[ n: set Node, right: Node->Node, left: Node->Node ]{
  rootedOne[n, left, right]
  isAcyclic[n, left, right]
	singleParent[n, left, right]
  isValidNoCommon[n, left, right] 
}

pred showValidTrees {
	some Node
	isTreeInstance[Node, right, left]
}

run showValidTrees for 3-- Node




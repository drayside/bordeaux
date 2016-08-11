sig Node {next: lone Node}

pred isAcyclic[nodes: set Node, next1: Node -> Node] {
	all node : nodes | node not in node.^next1
}

pred singleParent[nodes: set Node, next1: Node -> Node] {
	// all n1, n2 : nodes | n1 != n2 => n1.next1 != n2.next1
	all disj n1, n2 : nodes | n1.next1 != n2.next1
}

pred hello {

}

pred hi {

}

fact {
	isAcyclic[Node, next]
	singleParent[Node, next]
}

/*
assert instanceCheck {
	isListInstance[Node, next]
} 

check instanceCheck for 10
*/

run {} for 10


// Borrowed from http://stackoverflow.com/questions/15651231/doubly-linked-list-in-alloy
sig Node {
    nxt: set Node,
    prv: set Node,
}

sig Head, Tail extends Node{}

pred validDLL{
	Node = Head.*nxt
    some Node => one Tail
    no ^nxt & iden // no cycles
    nxt = ~prv     // symetric   
    no prv[Head]   // head has no prv
    no nxt[Tail]   // tail has no nxt
    Head.^nxt = Node.^nxt // all nodes in nxt are reachable from head
}


--run validDLL for 4

pred structural[]{
	all n: Node| lone n.nxt
	all n: Node| lone n.prv
	lone Head
	lone Tail
}

pred Not_structural[]{
	not structural
}

pred Not_validDLL{
	not validDLL
}

pred normal[]{
	structural
	validDLL
}

pred withStructural[]{
	Not_validDLL
	Not_structural
}

run normal for 4
run withStructural for 4

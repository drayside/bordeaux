// Borrowed from http://stackoverflow.com/questions/15651231/doubly-linked-list-in-alloy
sig Node {
    nxt: lone Node,
    prv: lone Node,
}

lone sig Head, Tail extends Node{}

pred validDLL{
	Node = Head.*nxt
    some Node => one Tail
    no ^nxt & iden // no cycles
    nxt = ~prv     // symetric   
    no prv[Head]   // head has no prv
    no nxt[Tail]   // tail has no nxt
    Head.^nxt = Node.^nxt // all nodes in nxt are reachable from head
}


run validDLL for 4

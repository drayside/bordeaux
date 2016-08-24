// Borrowed from http://stackoverflow.com/questions/15651231/doubly-linked-list-in-alloy
sig Node {
    nxt: lone Node,
    prv: lone Node,
}

lone sig Head, Tail extends Node{}

pred validDLL{

    no ^nxt & iden // no cycles
    
}

run validDLL for 4

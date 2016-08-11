/**
* This model is created for elaborating the mutation idea.
**/

sig Node{
	nxt:  set  Node}
one sig Head extends Node{}

pred acyclic{
	all n: Node| !( n in n.^(nxt) )
}

pred declarativeFormulaForNext{
	all n:Node | one n.nxt
}


pred linearList{ 
  one n: Node| Node = n.*nxt
}

pred connected{
  one n:Node| no n.nxt and all n':Node-n| one n'.nxt
}

pred singleHead{
  no Head.~nxt and all n': Node-Head| one n'.~nxt
}


check{
  ( declarativeFormulaForNext and
    acyclic //and
//    connected and
//    singleHead
) implies linearList   
} for 3

sig Node{ nxt:  set Node}
sig Head extends Node{}

pred acyclic{
  all n: Node| !( n in n.^(nxt) )
}

pred declarativeFormulaForNext_fixed{
  all n:Node | lone n.nxt
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

pred SinglyLinkedLists[]{
  acyclic 
  connected
  singleHead
}

--run SinglyLinkedLists for 3

pred structural[]{
	all n: Node| lone n.nxt
	one Head
}

pred Not_structural[]{
	not structural
}

pred Not_SinglyLinkedLists[]{
	not SinglyLinkedLists
}

pred withStructural[]{
	Not_SinglyLinkedLists
	Not_structural
}

pred withoutStructural[]{
	Not_SinglyLinkedLists
	structural
}

pred normal[]{
	SinglyLinkedLists
	structural
}

run normal for 3

run withStructural for 3

run withoutStructural for 3




--uniq
sig Node{val:Int}
--val != -1

abstract
//uniq 
sig Edge{
	src:  Node,
	dest:   Node
}{	
--	src!=dest
--	not(src.col = Red and dest.col = Red)
}


uniq
sig rightEdge extends Edge{}{
	src!=dest
--	src.val < dest.val
	dest.val != Int.max => dest.val in 	src.val.^next
}


uniq
sig leftEdge extends Edge{}{
	src!=dest
--	src.val > dest.val
	src.val != Int.min => dest.val !in 	src.val.^next
}

uniq 
sig BST {
	e: set Edge,
	rt: lone Node}{
	let bin={n',n'':Node|some e':e | n'=e'.src and n''=e'.dest}|
	(e!=none) =>{
		--Any node has at most one right or left edge
		all n: Node | (lone e':e&leftEdge|e'.src = n) 
							and (lone e'':e&rightEdge | e''.src = n)
		--Any node in tree is  reachable from the root
		one r: e.(src +dest)| e.(src +dest) =  r.*bin and rt=r
		--Any node has exactly one incoming edge except root
		all n:e.(src +dest)-rt |  one {e':e|e'.dest = n} and no {e':e|e'.dest = rt}
		--Any node's value is less than any node in the right subtree
		all n:e.(src +dest) | all i: 
					{p:Node | one l:rightEdge&e | (l.src = n) and (p in (l.dest).*bin)}
					.val | 
						--  n.val <= i		
						((n.val != Int.max) =>	(i in (n.val).^next))
		--Any node's value is more than any node in the left subtree
		all n:e.(src +dest) | all i: 
					{p:Node | one l:leftEdge&e | (l.src = n) and (p in (l.dest).*bin)}
					.val | 
						--	n.val >= i		
							((i != Int.max) => (n.val in i.^next))
		}
	}

fun nodes2[r:BST]:Node{
	{n:Node | n in r.rt.*(binaryEdges[r.e])}
}

fun binaryEdges[e:Edge]:Node->Node{
	{n,n':Node|some e':e | n=e'.src and n'=e'.dest}
}

pred insert[r,r':BST, i:Int]{
	nodes2[r'].val = i + nodes2[r].val
	i ! in nodes2[r].val
--i=	nodes2[r'].val - nodes2[r].val
}

pred remove[r,r':BST, i:Int]{
--	i = nodes2[r].val - nodes2[r'].val 

	nodes2[r].val = i + nodes2[r'].val
	i ! in nodes2[r'].val
}

pred InsertORRemove{
	--Any state can be left either by inserting or removing a value
	not(	
		all  r: BST |some i:Int,r':BST| ( insert[r,r',i] or remove[r,r',i])
//		all l: List | some i:Int,l':List-l| insert[l,l',i] or remove[l,l',i]
	)
//	some l:List | no l.head and no l.links
}

$INST_I

run InsertORRemove for i


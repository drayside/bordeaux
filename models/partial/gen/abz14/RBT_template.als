abstract sig Color{}

one sig Red,Black extends Color{}

--uniq
sig Node{val:Int,col:Color}--{val in 0+1+2+3}//+4+5+6+7+8+9}

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
sig leftEdge extends Edge{}{
	src!=dest
	not(src.col = Red and dest.col = Red)
--	src.val > dest.val
	src.val != Int.max => src.val in 	dest.val.^next
}

uniq
sig rightEdge extends Edge{}{
	src!=dest
	not(src.col = Red and dest.col = Red)
--	src.val < dest.val
	dest.val != Int.max => dest.val in 	src.val.^next
}

uniq sig RBT {
	e: set Edge,
	rt: lone Node}{
	let bin={n',n'':Node|some e':e | n'=e'.src and n''=e'.dest}|
	(e!=none) =>{
		--Any node has at most one right or left edge
		all n:Node | (lone e':e&leftEdge|e'.src=n) 
							and (lone e'':e&rightEdge | e''.src in n)
		--Any node in tree is  reachable from the root
		one r: e.(src +dest)| e.(src +dest) =  r.*bin and rt=r
		--Any node has exactly one incoming edge except root
		all n:e.(src +dest)-rt |  one {e':e|e'.dest = n} and no {e':e|e'.dest = rt}
		--Root is colored in Black
		rt.col=Black
		--The color of any item is unique in a tree
		all disj n',n'': e.(src +dest) | n'.val = n''.val => n'.col =n''.col
		--Any node's value is less than any node in the right subtree
		all n:e.(src +dest) | all i: 
					{p:Node | one l:rightEdge&e | (l.src = n) and (p in (l.dest).*bin)}
					.val | --n.val <= i	
					((n.val != Int.max) =>	(i in (n.val).^next))	
		--Any node's value is more than any node in the left subtree
		all n:e.(src +dest) | all i: 
					{p:Node | one l:leftEdge&e | (l.src = n) and (p in (l.dest).*bin)}
					.val | --n.val >= i		
					((i != Int.max) => (n.val in i.^next))
		--Both Red node's childeren are Red
		all n:e.(src +dest)| n.col = Red =>
					((no {p:Node|one l:rightEdge&e|(l.src=n) and (p=l.dest)} 	or  
					{p:Node|one l:rightEdge&e|(l.src=n) and (p=l.dest)}.col=Black) 
					and 
					(no {p:Node|one l:leftEdge&e|(l.src=n) and (p=l.dest)} or  
					{p:Node|one l:leftEdge&e | (l.src=n) and (p=l.dest)}.col=Black))		
		--All paths starting from a node have the same number of black nodes
		all n, n': e.(src +dest) |
					((no {p:Node | one l:leftEdge&e | (l.src = n) and (p = l.dest)} or 
					no {p:Node | one l:rightEdge&e | (l.src = n) and (p = l.dest)}) 
						and
					(no {p:Node | one l:leftEdge&e | (l.src = n') and (p = l.dest)} or 
					no {p:Node | one l:rightEdge&e | (l.src = n') and (p = l.dest)}))
					=>
					(#{ p: e.(src +dest) |n in p.*bin and p.col = Black } =
					#{ p: e.(src +dest) |n' in p.*bin and p.col = Black })
	}else{
		(no rt) or	(rt.col = Black)}}



fun nodes2[r:RBT]:Node{
	{n:Node | n in r.rt.*(binaryEdges[r.e])}
}

fun binaryEdges[e:Edge]:Node->Node{
	{n,n':Node|some e':e | n=e'.src and n'=e'.dest}
}

pred insert[r,r':RBT, i:Int]{
	nodes2[r'].val = i + nodes2[r].val
	i ! in nodes2[r].val
--i=	nodes2[r'].val - nodes2[r].val
}

pred remove[r,r':RBT, i:Int]{
--	i = nodes2[r].val - nodes2[r'].val 

	nodes2[r].val = i + nodes2[r'].val
	i ! in nodes2[r'].val
}


/*
pred insert[l,l':List, i:Int]{
	i ! in l.links.(src +dest).val
	l'.links.(src +dest).val = i + l.links.(src +dest).val}

pred remove[l,l':List, i:Int]{
	l.links.(src +dest).val = i + l'.links.(src +dest).val
	i ! in l'.links.(src +dest).val}

pred lookup[l:List, i:Int]{
	i in l.links.(src +dest).val}
*/

pred InsertORRemove{
	--Any state can be left either by inserting or removing a value
	not(	
		all  r: RBT |some i:Int,r':RBT| ( insert[r,r',i] or remove[r,r',i])
//		all l: List | some i:Int,l':List-l| insert[l,l',i] or remove[l,l',i]
	)
//	some l:List | no l.head and no l.links
}

$INST_I
//check InsertORRemove for 3 but exactly 50 List



run InsertORRemove for i


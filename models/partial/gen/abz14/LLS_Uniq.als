uniq sig Node{val:Int}{gte[val,0] and lte[val,3]}

uniq sig Link{ src: Node, dest: Node}{
	--noself loop
	src!=dest
	dest.val != Int.max => dest.val in 	src.val.^next
}

uniq sig List{head:lone Node, links: set Link}{
	 links!=none =>{
		--All the nodes are reachable from the head
		({ links.src + links.dest } = 
			head.*({n',n'':Node|some l':links | n'=l'.src and n''=l'.dest}))
		--last node has no outgoing link
		(one n:{ links.src + links.dest } | n !in links.src )
		--The links are linear
		(all n: {links.src+links.dest} | lone l: links | n = l.src)
	} 
}

fun nodes[r:List]:Node{
	{n:Node | n in r.head.*(binaryEdges[r.links])}
}

fun nodes[links: set Link]:set Node{
	{links.src + links.dest}
}

fun binaryEdges[e:Link]:Node->Node{
	{n,n':Node|some e':e | n=e'.src and n'=e'.dest}
}

pred insert[r,r':List, i:Int]{
	nodes[r'].val + i = nodes[r].val
--	nodes[r'].val = i + nodes[r].val
	i ! in nodes[r].val
	
}

pred remove[r,r':List, i:Int]{
	nodes[r].val + i =  nodes[r'].val
--	nodes[r].val = i +  nodes[r'].val
	i ! in nodes[r'].val

}

pred InsertORRemovePred{
	--Any state can be left either by inserting or removing a value
		all  r: List |some i:Int,r':List| ( insert[r,r',i] or remove[r,r',i]) 
}

assert InsORRmvAsrt{
	InsertORRemovePred
}

pred NoInsRmvInrPred{
	some r:List | no r': List | some i:Int | ( insert[r,r',i] or remove[r,r',i]) 
}

pred NoInsRmvOtrPred{
	some r:List | some i:Int | no r': List | ( insert[r,r',i] or remove[r,r',i]) 
}

assert eqSATNoInrAsrt{
	NoInsRmvInrPred <=> (not InsertORRemovePred)
}

assert eqSATNoOtrAsrt{
	NoInsRmvOtrPred <=> (not InsertORRemovePred)
}

assert eqSATNoOtrInr{
	NoInsRmvInrPred <=> NoInsRmvOtrPred
}

inst i {
	0,
	3 Int
	--Since Nodes are generated, their scope are set in Node's appended fact.
}

//check InsORRmvAsrt for i

//run NoInsRmvInrPred for i

//run NoInsRmvOtrPred for i

//check eqSATNoInrAsrt for i

//check eqSATNoOtrAsrt for i

check eqSATNoOtrInr for i



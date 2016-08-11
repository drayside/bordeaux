module LLS_M

open util/integer
--uniq
sig Node{val:Int}

--uniq
sig Link{ src: Node, dest: Node}{
	--noself loop
	src!=dest
	dest.val != Int.max => dest.val in 	src.val.^next
}

fun nodes[l: set Link]:set Node{
	{n:Node| some l':l| n=l'.src or n=l'.dest }
}

fun bin[l:Link]:Node->Node{
	{n',n'':Node|some l':l | n'=l'.src and n''=l'.dest}
}

--uniq
sig List{head:lone Node, links: set Link}{
	 links!=none =>(--All the nides are reachable from the head
		({n:Node| some l':links| n=l'.src or n=l'.dest } = 
			head.*({n',n'':Node|some l':links | n'=l'.src and n''=l'.dest}))
	and
	--nodes[links] = head.*((bin[links]))
	--last node has no outgoing link
		(one n:{n:Node| some l':links| n=l'.src or n=l'.dest } | n !in links.src )
	and
	--The links are linear
		(all n: {links.src+links.dest} | lone l: links | n = l.src)
	--Node = nodes[linkes]
	) 
	//no links => ( head!=none)
}

/*fact unique{
	all disj n,n':Node | n.val!=n'.val
	all disj l,l':Link | l.src!=l'.src or l.dest!=l'.dest
	some List
}*/


fun nodes2[r:List]:Node{
	{n:Node | n in r.head.*(binaryEdges[r.links])}
}

fun binaryEdges[e:Link]:Node->Node{
	{n,n':Node|some e':e | n=e'.src and n'=e'.dest}
}

pred insert[r,r':List, i:Int]{
	nodes2[r'].val = i + nodes2[r].val
	i ! in nodes2[r].val
--i=	nodes2[r'].val - nodes2[r].val
}

pred remove[r,r':List, i:Int]{
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
		all  r: List |some i:Int,r':List| ( insert[r,r',i] or remove[r,r',i])
//		all l: List | some i:Int,l':List-l| insert[l,l',i] or remove[l,l',i]
	)
//	some l:List | no l.head and no l.links
}


fact uniq{
	all disj n,n':Node | n.val!=n'.val //or n.col!=n'.col
	all disj e,e':Link | e.src != e'.src or e.dest!=e'.dest
	all disj r,r':List | r.head != r'.head or r.links!=r'.links
}

//check InsertORRemove for 3 but exactly 50 List





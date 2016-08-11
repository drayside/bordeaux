open util/ordering[A] as As
open util/ordering[C] as Cs


sig A{p:A  ->  Int}



sig C{q:C -> Int}

//uniq
sig B{r: A -> C}{ 
}

-------------------------------------------------------------------
fun nextA[]: A-> one A{
	{ a,a': A| a = As/last => a'=As/first else a' = As/next[a] }
}

fun nextC[]: C-> one C{
	{ c, c': C| c = Cs/last => c'=Cs/first else c' = Cs/next[c] }
}
-------------------------------------------------------------------

fact uniq{
    	all disj b,b':B | b.r != b'.r
}

fact path{
	all a:A | 0 = p[a,a]
	all disj a,a':A | a' = a.nextA => 1 = p[a,a']
    all disj a,a',a'':A | (a' = a.nextA ) => p[a,a''] = add[1, p[a',a'']] 

	all c:C | 0 = q[c, c ]
	all disj c,c':C | c' = c.nextC => 1 = q[c, c' ]
	all disj c, c', c'': C | (c' = c.nextC ) => q[c, c'' ] = add[1, q[c', c'' ] ] 

}
-------------------------------------------------------------------
//Sigma Function for each Signature
fun mapA[a:A]: one A{
	{ a': A| a = As/last => a'=As/first else a' = As/next[a] }
}

fun mapC[c: C ]: one C{
	{ c': C| c = Cs/last => c'=Cs/first else c' = Cs/next[c] }
}

fun mapAn[a:A, n: Int]: one A{
	    {a': A | p[a,a'] = n}
}

fun mapCn[c: C, n: Int ]: one C{
	    {c': C | q[c, c' ] = n}
}

-------------------------------------------------------------------
//Sigma function for permutating tuples
fun mapA'C[t:A->C]: A->C{
	{a:A,c:C | 	
		 (some a': t.C | one c': A.t| 
					a'->c' in t and  a in mapA[a'] and c = c' ) }
}

fun mapAC'[t:A->C]: A->C{
	{a:A,c:C | 	
		 (some a': t.C | one c': A.t| 
					a'->c' in t and  a=a' and c in mapC[c'] ) }
}

fun mapA'Cn[t:A->C, n: Int]: A->C{
	{a:A,c:C | 	
		 (some a': t.C | one c': A.t| 
					a'->c' in t and  a in mapAn[a', n] and c = c' ) }
}

fun mapAC'n[t:A->C, n:Int]: A->C{
	{a:A,c:C | 	
		 (some a': t.C | one c': A.t| 
					a'->c' in t and  a=a' and c in mapCn[c', n ] ) }
}

-------------------------------------------------------------------
//Sigma function for permutating only one atom of a tuple of a signature atom
pred sigmaA[b, b': B ]{
	 b'.r = mapA'C[b.r]
}

pred sigmaC[b, b': B ]{
	 b'.r = mapAC'[b.r]
}

pred sigmaAn[b, b': B, n:Int ]{
	 b'.r = mapA'Cn[b.r, n]
}

pred sigmaCn[b, b': B, n: Int ]{
	 b'.r = mapAC'n[b.r, n]
}

fun sigmaAf[]: B-> B{
	     {b, b': B| sigmaA[b, b' ] }
}

fun sigmaCf[]:B-> B{
	     {b, b': B| sigmaC[b, b' ] }
}

fun sigmaAf[n: Int]: B-> B{
	     {b, b': B| sigmaAn[b, b',n ] }
}

fun sigmaCfn[n: Int]:B-> B{
	     {b, b': B| sigmaCn[b, b', n] }
}
-------------------------------------------------------------------
//Sigma function for permutating any atom of any tuple in a signatures atom
pred sigmaAC[b, b': B ]{
	 sigmaA[b, b' ] or sigmaC[b, b'] 
}

pred sigmaACnm[b, b': B, n,m: Int ]{
	(sigmaAn[b, b', n ] or sigmaCn[b, b', m]) //and (some b.r => b!=b' )
}

pred sigmaACnmE1[b, b': B, n,m: Int ]{	
	sigmaAn[b, b', n ]  
	not sigmaCn[b, b', m] 
	m = 0
}

pred sigmaACnmE2[b, b': B, n,m: Int ]{	
	not sigmaAn[b, b', n ]  
	sigmaCn[b, b', m] 
	n = 0
}

pred sigmaACnmE3[b, b': B, n,m: Int ]{	
	sigmaAn[b, b', n ]  
	sigmaCn[b, b', m] 
}

pred sigmaACnmE[b, b': B, n,m: Int]{
	{
		sigmaACnmE1[b, b' ,n ,m ]
		not sigmaACnmE2[b, b' ,n ,m ]
		not sigmaACnmE3[b, b' ,n ,m ]
	}or
	{
		not sigmaACnmE1[b, b' ,n ,m ]
		sigmaACnmE2[b, b' ,n ,m ]
		not sigmaACnmE3[b, b' ,n ,m ]
	}or
	{
		not sigmaACnmE1[b, b' ,n ,m ]
		not sigmaACnmE2[b, b' ,n ,m ]
		sigmaACnmE3[b, b' ,n ,m ]
	}
}

fun sigmaACf[]: B->B{
	     {b, b': B| sigmaAC[b, b' ] }
}

fun sigmaACfnm[n,m: Int]: B->B{
	     {b, b': B| sigmaACnm[b, b', n, m ] }
}


-------------------------------------------------------------------
//checking add, remove,  rename, and faulty add predicates.

pred pAddPermutateA_OneOne{
//	 some c,c':C, a,a',a'',a''': A, b1, b2, b3, b4: B, i, j: Int | i in 0+1 and j in 0+1 and sigmaACi[b1,b3,a->a', c->c']
 some c,c':C, a,a': A, b1, b2, b3, b4: B, n,m: (0+1) |
/*							and //sigmaACi[b1,b3,i,j]
							( ( sigmaAn[b1,b3,i] and (  (some b1.r and b3!=b1) => a' = mapAn[a,i] else a'=a ) )
								=>
							 (sigmaCn[b1,b3,j] and ( (some b1.r and b3!=b1) => c' = mapCn[c,j] else c'=c ) ) )
                           and
							( (sigmaAn[b2,b4,i] and ( (some b2.r and b4!=b2) => a'' = mapAn[a,i] else a''=a) ) 
								=>
							 (sigmaCn[b2,b4,j] and ( (some b2.r and b4!=b2) => c'' = mapCn[c,j] else c''=c) ) )
and c'=c'' and a'=a'' 
//		                        and
//                          a''' = mapAn[a',i]
                        and*/
						sigmaACnmE[b1,b3,n, m]
							and
						sigmaACnmE[b2,b4,n, m]
							and
						a' = mapAn[a, n]
							and
						c' = mapCn[c, m]
							and
                     	 !( add[b1,a,c,b2] <=> add[b3 ,a' ,c' ,b4 ] )
// !( remove[b1,a,c,b2] <=> remove[b3 ,a' ,c' ,b4 ] )
// !( renameA[b1,a,a',c,b2] <=> renameA[b3 ,a'' ,a''' ,c' ,b4 ] )
//                       !( add_not_fun[b1,a,c,b2] <=> add_not_fun[b3 ,a' ,c' ,b4 ] )


}
run pAddPermutateA_OneOne //for 0 but 3 Int,  exactly 2 A, exactly 2 C, exactly 16 B

pred pRemovePermutateA_OneOne{
	some c,c':C, a,a': A, b1, b2, b3, b4: B, n,m: (0+1) |
				sigmaACnmE[b1,b3,n, m] and sigmaACnmE[b2,b4,n, m] and
				a' = mapAn[a, n] and c' = mapCn[c, m] and
				!( remove[b1,a,c,b2] <=> remove[b3 ,a' ,c' ,b4 ] )
}
run pRemovePermutateA_OneOne //for 0 but 3 Int,  exactly 2 A, exactly 2 C, exactly 16 B

pred pRenamePermutateA_OneOne{
	some c,c':C, a1,a2,a3,a4: A, b1, b2, b3, b4: B, n, m: (0+1) |
				sigmaACnmE[b1,b3,n, m] and sigmaACnmE[b2,b4,n, m] and
				a3 = mapAn[a1, n] and a4 = mapAn[a2, n] and c' = mapCn[c, m] and
				!( renameA[b1,a1,a2,c,b2] <=> renameA[b3 ,a3 ,a4 ,c' ,b4 ] )
}
run pRenamePermutateA_OneOne //for 0 but 3 Int,  exactly 2 A, exactly 2 C, exactly 16 B

pred pFaultyAddPermutateA_OneOne{
	some c,c':C, a,a': A, b1, b2, b3, b4: B, n,m: (0+1) |
				sigmaACnmE[b1,b3,n, m ] and sigmaACnmE[b2,b4,n, m ] and
				a' = mapAn[a, n] and c' = mapCn[c, m] and
				!( add_not_fun[b1,a,c,b2] <=> add_not_fun[b3 ,a' ,c' ,b4 ] )
}
run pFaultyAddPermutateA_OneOne for 2 but 3 Int, 3 B, 3 A //for 0 but 3 Int,  exactly 2 A, exactly 2 C, exactly 16 B


-------------------------------------------------------------------
//Operations

pred add[b: B, a: A, c:C, b': B]{
    	b'!=b 
    	b.r = b'.r - a->c
    	a->c !in b.r	
}

pred add_not_fun[b: B, a: A, c:C, b': B]{
     	b'!=b     	
     	( 
			(b.r = b'.r - a->c and a->c !in b.r	) 
					or
	       ( ( As/first->Cs/first +As/last->Cs/last  = b.r ) and (add[ #b.r,1] = #b'.r) )
		) //(b.r = b'.r - (b'.r).C->Cs/last ) ) )
}

pred remove[b: B, a: A, i:C, b': B]{
    	b'!=b 
    	b'.r  = b.r - a->i
    	a->i in b.r 
}


pred renameA[b: B, a: A, a':A, c:C,  b': B]{
			    a != a'
	(b.r) + a'->c = b'.r + a->c
    	a->c !in b'.r
}

pred renameC[b: B, a: A, c:C, c':C,  b': B]{
	    c != c'
	(b.r) + a->c' = b'.r + a->c
    a->c !in b'.r
}

-------------------------------------------------------------------
//Generators
fun showAddEdges[]:B->B{
	{b,b':B| some c:C, a:A | add[b,a,c,b']}
}

fun showAdd_not_fun_Edges[]:B->B{
	{b,b':B| some c:C, a:A | add_not_fun[b,a,c,b']}
}

fun showRemoveEdges[]:B->B{
	{b,b':B| some c:C, a:A | remove[b,a,c,b']}
}

fun showAddRemoveEdges[]:B->B{
	{b,b':B| some c:C, a:A | remove[b,a,c,b'] or add[b,a,c,b']}
}


fun showRenameAEdges[]:B->B{
	{b,b':B| some c:C, a,a':A | renameA[b, a, a', c, b' ]}
}
fun showRenameCEdges[]:B->B{
	{b,b':B| some c,c':C, a:A | renameC[b, a, c, c', b' ]}
}


fun showpermuteAEdges[]:B->B{
	{b,b':B| sigmaA[b,b']}
}
fun showpermuteCEdges[]:B->B{
	{b,b':B| sigmaC[b,b']}
}
fun showpermuteACEdges[]:B->B{
	{b,b':B| sigmaC[b,b'] or sigmaA[b,b']}
}

-------------------------------------------------------------------
pred pRenameAPermutateA{
	 some b: B| some c:C, a,a': A, b': B|  renameA[b,a,a',c,b'] and sigmaA[b,b']
}
run pRenameAPermutateA for 3 but exactly 2 B

pred pRenameAPermutateC{
	 some b: B| some c:C, a,a': A, b': B|  renameA[b,a,a',c,b'] and sigmaC[b,b']
}
run pRenameAPermutateC for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B

pred pRenameAPermutateAC{
	 some b: B| some c:C, a,a': A, b': B|  renameA[b,a,a',c,b'] and sigmaAC[b,b']
}
run pRenameAPermutateAC for 3 but 2 B


pred pRenameCPermutateA{
	 some b: B| some c, c':C, a: A, b': B|  renameC[b ,a ,c , c' ,b' ] and sigmaA[b,b']
}
run pRenameCPermutateA for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B

pred pRenameCPermutateC{
	 some b: B| some c, c':C, a: A, b': B|  renameC[b ,a ,c , c' ,b' ] and sigmaC[b,b']
}
run pRenameCPermutateC for 3 but 2 B

pred pRenameCPermutateAC{
	 some b: B| some c, c':C, a: A, b': B|  renameC[b ,a ,c , c' ,b' ] and sigmaAC[b,b']
}
run pRenameCPermutateAC for 3 but 2 B


pred pAddPermutateA{
	 some b: B| some c:C, a: A, b': B|  add[b,a,c,b'] and sigmaA[b,b']
}
run pAddPermutateA for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B
pred pAddPermutateC{
	 some b: B| some c:C, a: A, b': B|  add[b,a,c,b'] and sigmaC[b,b']
}
run pAddPermutateC for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B

pred pAddPermutateAC{
	 some b: B| some c:C, a: A, b': B|  add[b,a,c,b'] and sigmaAC[b,b']
}
run pAddPermutateAC for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B






pred pRemovePermutateA{
	 some b: B| some c:C, a: A, b': B|  remove[b,a,c,b'] and sigmaA[b,b']
}
run pRemovePermutateA for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B

pred pRemovePermutateC{
	 some b: B| some c:C, a: A, b': B|  remove[b,a,c,b'] and sigmaC[b,b']
}
run pRemovePermutateC for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B

pred pRemovePermutateAC{
	 some b: B| some c:C, a: A, b': B|  remove[b,a,c,b'] and sigmaAC[b,b']
}
run pRemovePermutateAC for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B



pred pAddRemovePermutateA{
	 some b: B| some c:C, a: A, b': B|  (add[b,a,c,b'] or remove[b,a,c,b']) and sigmaA[b,b']
}
run pAddRemovePermutateA for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B

pred pAddRemovePermutateC{
	 some b: B| some c:C, a: A, b': B|  (add[b,a,c,b'] or remove[b,a,c,b']) and sigmaC[b,b']
}
run pAddRemovePermutateC for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B

pred pAddRemovePermutateAC{
	 some b: B| some c:C, a: A, b': B|  (add[b,a,c,b'] or remove[b,a,c,b']) and sigmaAC[b,b']
}
run pAddRemovePermutateAC for 0 but 1 Int, exactly 2 A, exactly 2 C, exactly 16 B

-------------------------------------------------------------------
run {} for 0 but 3 Int, exactly 2 A, exactly 2 C, exactly 16 B

run {} for 0 but 4 Int, exactly 4 A, exactly 1 C, exactly 8 B

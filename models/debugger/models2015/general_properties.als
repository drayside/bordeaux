module general_properties

//no cycles or self-loops
pred acyclic [ r :univ->univ , t :univ ] {
	all x: t | x !in x.^r 
}

//no two-node cycles
pred antisymmetric [ r :univ->univ ] {
	~r & r in iden
}

pred antisymmetric3 [ r :univ->univ->univ ] {
	all x,y,z: univ | x->y->z in r => z->y->x !in r
}

//all possible tuples exist
pred complete [ r :univ->univ , t :univ ] {
	all x,y:t | x!=y => (x->y in r && y->x in ~r)
}

pred cyclic [ r :univ->univ->univ ] {
	all x,y,z: univ | (x->y->z in r) => (y->z->x in r)
}

//all elements in the domain map to at least one element in the range
pred functional [ r :univ->univ , t :univ ] { 
	all x:t | lone x.r
}

//all elements in the range are mapped to by at most one element in the domain
pred injective [ r :univ->univ , t :univ ] { 
	all x:t | lone r.x
}

//equivalent to defining r = set A -> one B -> set C 
/*pred innerinjective [ r :univ->univ ] {
	all x:r.univ | injective[x.r, univ.(x.r)]
}*/


//no self-loops
pred irreflexive [ r :univ->univ ] {
	no iden & r
}

pred irreflexive3 [ r :univ->univ ->univ] {
	no x:univ | x->x->x in  r
}

pred irreversible [ r :univ->univ ->univ] {
	(all x,y,z,u:univ| x->y->z in r  => y->x->u !in r) 
}

//all nodes have self-loops
pred reflexive [ r :univ->univ , t :univ ] {
	t <: iden in r 
}

pred regular [ r :univ->univ ->univ ] {
weaklyRegular[r]
all x,y,z,p,q:univ| x->y->p in r and x->z->q in r => x->y->z in r
}

//all elements in domain can reach all elements in range 
pred rootedAll [ r :univ->univ , t :univ ] {
	all root:t | t in root.*r
}

//one element in domain can reach all elements in range 
pred rootedOne [ r :univ->univ , t :univ ] {
	one root:t | t in root.*r
}

//all elements in domain can reach all elements in range 
pred stronglyConnected [ r :univ->univ , t :univ ] {
	all d,g:t | d != g => d in g.^r
}

//all elements in the range are mapped to by at least one element in the domain 
pred surjective [ r :univ->univ , t :univ ] {
	all x:t | some r.x
}

//undirectional relations
pred symmetric [ r :univ->univ ] {
	~r in r
}

//undirectional ternary relations
pred symmetric3 [ r :univ->univ ->univ ] {
	all x,y,z: univ | x->y->z in r => z->y->x in r
}

//all elements in the domain map to at most one element in the range
pred total [ r :univ->univ , t :univ ] { 
	all x:t | some x.r
}

//every node is directly connected to all reachable nodes
pred transitive [ r :univ->univ ] { 
	r. r in r
}

pred transitive3 [ r :univ->univ->univ ] { 
	(all x,y,z,u:univ| x->y->z in r and z->y->u in r => x->y->u in r) 
}

pred translative[ r :univ->univ->univ ] { 
	weaklyRegular[r]
	all x,y,z:univ| x->y->z in r => some u:univ| x->z->u in r or y->z->u in r
}

//all elements in domain reach or are reachable by all elements in range
pred weaklyConnected [ r :univ->univ , t :univ ] { 
all d,g:t | d != g => d in g.^(r +~ r)
}

pred weaklyTransitive [ r :univ->univ->univ ] { 
	(all x,y,u:univ| x->y->y in r and y->y->u in r => x->y->u in r) 
}

pred weaklyRegular[ r :univ->univ->univ ] { 
	(all x,y,z,p,q:univ| x->y->p in r and y->z->q in r => x->y->z in r) 
}

pred weaklyTranslative[ r :univ->univ->univ ] { 
	all x,y,z,p,q:univ| x->y->z in r and y->p->q in r => some u:univ| x->p->u in r
}


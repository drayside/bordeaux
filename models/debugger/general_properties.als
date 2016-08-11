module general_properties

pred antisymmetric3 [ r :univ->univ->univ ] {
	all x,y,z: univ | x->y->z in r => z->y->x !in r
}

pred cyclic [ r :univ->univ->univ ] {
	all x,y,z: univ | (x->y->z in r) => (y->z->x in r)
}

pred irreflexive3 [ r :univ->univ ->univ] {
	no x:univ | x->x->x in  r
}

pred irreversible [ r :univ->univ ->univ] {
	(all x,y,z,u:univ| x->y->z in r  => y->x->u !in r) 
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

//undirectional ternary relations
pred symmetric3 [ r :univ->univ ->univ ] {
	all x,y,z: univ | x->y->z in r => z->y->x in r
}

pred transitive3 [ r :univ->univ->univ ] { 
	(all x,y,z,u:univ| x->y->z in r and z->y->u in r => x->y->u in r) 
}

pred translative[ r :univ->univ->univ ] { 
	weaklyRegular[r]
	all x,y,z:univ| x->y->z in r => some u:univ| x->z->u in r or y->z->u in r
}

//all elements in domain can reach all elements in range 
pred stronglyConnected [ r :univ->univ , t :univ ] {
	all d,g:t | d != g => d in g.^r
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


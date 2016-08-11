module relational_properties

/*
 * Utilities for some common operations and constraints
 * on binary relations. The keyword 'univ' represents the
 * top-level type, which all other types implicitly extend.
 * Therefore, all the functions and predicates in this model
 * may be applied to binary relations of any type.
 *
 * author: Greg Dennis
 */

/** r is empty **/
pred empty3[r: univ -> univ -> univ]{
	no r
}

/** r is empty **/
pred empty[r: univ -> univ]{
	no r
}

/** returns the domain of a binary relation */
fun dom [r: univ->univ] : set (r.univ) { r.univ }

/** returns the range of a binary relation */
fun ran [r: univ->univ] : set (univ.r) { univ.r }

/** r is total over the domain s */
pred total [r: univ->univ, s: set univ] {
  all x: s | some x.r
}

/** r is a partial function over the domain s */
pred functional [r: univ->univ, s: set univ] {
  all x: s | lone x.r
}

/** r is a total function over the domain s */
pred function [r: univ->univ, s: set univ] {
  all x: s | one x.r
}

///////? it used to be s and I made it to t.
/** r is surjective over the codomain s or range*/
pred surjective [r: univ->univ, t: set univ] {
  all x: t | some r.x
}


///////? it used to be s and I made it to t.
/** r is injective */
pred injective [r: univ->univ, t: set univ] {
  all x: t | lone r.x
}

/** equivalent to defining r = set A -> one B -> set C*/
pred innerinjective [ r :univ->univ->univ ]{
  all x:r.univ.univ | injective[x.r, univ.(x.r)]
}

///////? it used to be s and I made it to t.
/** r is bijective over the codomain s */
pred bijective[r: univ->univ, t: set univ] {
  all x: t | one r.x
}

/** r is a bijection over the domain d and the codomain c */
pred bijection[r: univ->univ, s, t: set univ] {
  function[r, s] && bijective[r, t]
}

//Does it make any sense to have refexive property where domaind and range are different?
/** r is reflexive over the set s */
pred reflexive [r: univ -> univ, s: set univ] {
s<:iden in r
}

--Same as previous
/** r is irreflexive */
pred irreflexive [r: univ -> univ, s,t:univ] {
s = t
no iden & r
}

--Same as previous
/** r is symmetric */
pred symmetric [r: univ -> univ, s,t: univ] {
s = t
~r in r
}

--Same as previous
/** r is anti-symmetric */
pred antisymmetric [r: univ -> univ, s,t: univ] {
s = t
~r & r in iden}

--Same as previous
/** r is transitive */
pred transitive [r: univ -> univ, s,t: univ] {
s = t
r.r in r}

//Not sure wether it makes sences. But if the type of domain and range are different, then
//the relation `r` is absloutly acyclic.
/** r is acyclic over the set s */
pred acyclic[r: univ->univ, s: set univ] {
  all x: s | x !in x.^r
}


/** r is complete over the set s */
/*pred complete[r: univ->univ, s: univ] {
  all x,y:s | (x!=y => x->y in (r + ~r))
}*/
//compelte and complete2 are equivalent, if domain and range come from the same set.
pred complete[r: univ->univ, s: univ, t:univ] {
  all x:s, y:t | (x!=y => x->y in (r + ~r))
}

//Same as reflexive
/** r is a preorder (or a quasi-order) over the set s */
pred preorder [r: univ -> univ, s,t: set univ] {
  reflexive[r, s]
  transitive[r,s,t]
}

//Same as reflexive
/** r is an equivalence relation over the set s */
pred equivalence [r: univ->univ, s,t: set univ] {
  preorder[r, s,t]
  symmetric[r,s,t]
}

//Same as reflexive
/** r is a partial order over the set s */
pred partialOrder [r: univ -> univ, s,t: set univ] {
  preorder[r, s,t]
  antisymmetric[r,s,t]
}

//Same as reflexive, although there is a `complete` property in the a total order,
//but since `partialOrder` takes a set, then `totalOrder` is defined over a set.
/** r is a total order over the set s */
pred totalOrder [r: univ -> univ, s,t: set univ] {
  partialOrder[r, s,t]
  complete[r, s,t]
}

/**rootedAll: all elements in domain can reach all elements in range*/
/*pred rootedAll [r: univ->univ, t: univ]{
  all root:t | t in root.*r
}*/
//rootedAll2 can be replaced with rootedAll when both s and t are equal.
pred rootedAll [r: univ->univ, s:univ, t: univ]{
  all root:s | t in root.*r
}

/**rootedOne: one element in domain can reach all elements in range*/
/*pred rootedOne [r: univ->univ, t: univ]{
  one root:t | t in root.*r
}*/
pred rootedOne [r: univ->univ, s:univ, t: univ]{
  one root:s | t in root.*r
}

/**stronglyConnected: all elements in domain can reach all elements in range */
/*pred stronglyConnected [ r :univ->univ , t :univ ] {
  all disj d,g: t | d in g.^r
}*/
pred stronglyConnected [ r :univ->univ , s:univ, t :univ ] {
  all d: t | all g: s - d | d in g.^r
}

/**weaklyConnected: all elements in domain reach or are reachable by all elements in range */
/*pred weaklyConnected [ r :univ->univ , t :univ ] {
  all disj d,g: t | d in g.^(r + ~r)
}*/
pred weaklyConnected [ r :univ->univ,  s:univ, t :univ ] {
  all d: t | all g: s - d  | d in g.^(r + ~r)
}

pred tripleSameType[s,m,t:univ]{
	s = m
	s = t
	m = t
}

----------------------Ternary relations
pred antisymmetric3 [ r :univ->univ->univ, s,m,t:univ ] {
	//Type of x->y->z has to be the same as z->y->x
	tripleSameType[s,m,t]
	all x,y,z: univ | x->y->z in r => z->y->x !in r
}

pred cyclic [ r :univ->univ->univ, s,m,t:univ ] {
	tripleSameType[s,m,t]
	all x,y,z: univ | (x->y->z in r) => (y->z->x in r)
}

pred irreflexive3 [ r :univ->univ ->univ, s,m,t:univ] {
	tripleSameType[s,m,t]
	no x:univ | x->x->x in  r
}

pred irreversible [ r :univ->univ ->univ, s,m,t:univ] {
	tripleSameType[s,m,t]
	(all x,y,z,u:univ| x->y->z in r  => y->x->u !in r) 
}

pred regular [ r :univ->univ ->univ, s,m,t:univ ] {
	tripleSameType[s,m,t]
	weaklyRegular[r,s,m,t]
	all x,y,z,p,q:univ| x->y->p in r and x->z->q in r => x->y->z in r
}

//undirectional ternary relations
pred symmetric3 [ r :univ->univ ->univ, s,m,t:univ ] {
	tripleSameType[s,m,t]
	all x,y,z: univ | x->y->z in r => z->y->x in r
}

pred transitive3 [ r :univ->univ->univ, s,m,t:univ ] { 
	tripleSameType[s,m,t]
	(all x,y,z,u:univ| x->y->z in r and z->y->u in r => x->y->u in r) 
}

pred translative[ r :univ->univ->univ, s,m,t:univ ] {
	tripleSameType[s,m,t] 
	weaklyRegular[r,s,m,t]
	all x,y,z:univ| x->y->z in r => some u:univ| x->z->u in r or y->z->u in r
}

/*
//all elements in domain can reach all elements in range 
pred stronglyConnected [ r :univ->univ , t :univ ] {
	all d,g:t | d != g => d in g.^r
}

//all elements in domain reach or are reachable by all elements in range
pred weaklyConnected [ r :univ->univ , t :univ ] { 
all d,g:t | d != g => d in g.^(r +~ r)
}*/

pred weaklyTransitive [ r :univ->univ->univ, s,m,t:univ ] { 
	tripleSameType[s,m,t]
	(all x,y,u:univ| x->y->y in r and y->y->u in r => x->y->u in r) 
}

pred weaklyRegular[ r :univ->univ->univ, s,m,t:univ ] { 
	tripleSameType[s,m,t]
	(all x,y,z,p,q:univ| x->y->p in r and y->z->q in r => x->y->z in r) 
}

pred weaklyTranslative[ r :univ->univ->univ, s,m,t:univ ] { 
	tripleSameType[s,m,t]
	all x,y,z,p,q:univ| x->y->z in r and y->p->q in r => some u:univ| x->p->u in r
}


-----------------------------------
/**
*	In the following properties, the relation is ternary and defined as r:s->m->t
**/
//one s
pred oneDom[r:univ->univ->univ, s,m,t:univ]{
	one (r.t).m
}

//one m
pred oneMiddle[r:univ->univ->univ, s,m,t:univ]{
	one s.(r.t)
}

//one t
pred oneRange[r:univ->univ->univ, s,m,t:univ]{
	one m.(s.r)
}

//tripple functional. for every x in domain, there is pair in t.
pred tripleTotal [r:univ->univ->univ, s,m,t:univ] {
  all x: s | some x.r
}

/** r is a partial function over the domain s */
pred tripleFunctional [r:univ->univ->univ, s,m,t:univ] {
  all x: s | lone x.r
}

/** r is a total function over the domain s */
pred tripleFunction [r: univ->univ->univ, s,m,t: set univ] {
  all x: s | one m.(x.r)
}

pred tripleSurjective [r:univ->univ->univ, s,m,t:univ] {
  all x: t | some (r.x).m
}


///////? it used to be s and I made it to t.
/** r is injective */
pred tripleInjective [r: univ->univ->univ, s,m,t: set univ] {
  all x: t | lone (r.x).m
}

///////? it used to be s and I made it to t.
/** r is bijective over the codomain s */
pred tripleBijective[r: univ->univ->univ, s,m,t: set univ] {
  all x: t | one (r.x).m
}

/** r is a bijection over the domain d and the codomain c */
pred tripleBijection[r: univ->univ->univ, s,m,t: set univ] {
  tripleFunction[r, s,m,t] and tripleBijective[r, s,m,t]
}

pred noDiamond [r:univ->univ->univ, s,m,t:univ] {
	all x:s, disj y,w:m, z:t | x->y->z in r => x->w->z ! in r
}



//rootedAll2 can be replaced with rootedAll when both s and t are equal.
pred tripleSourcesAll [r: univ->univ->univ, s, m, t: univ]{
  all root:s | t in m.(root.r)
}

/**rootedOne: one element in domain can reach all elements in range*/
/*pred rootedOne [r: univ->univ, t: univ]{
  one root:t | t in root.*r
}*/
pred tripleRootedOne [r: univ->univ->univ, s,m, t: univ]{
  one root:s | t in m.(root.r)
}
//is this a forest. do we have a single tree an all other nodes from s does not go anywhere.

/**stronglyConnected: all elements in domain can reach all elements in range */
/*pred stronglyConnected [ r :univ->univ , t :univ ] {
  all disj d,g: t | d in g.^r
}*/
pred tripleStronglyConnected [ r :univ->univ->univ , s,m, t :univ ] {
  all a:s, b:m, c:t | a->b->c in r
}


pred tripleComplete[r: univ->univ->univ, s,m, t:univ] {
  all x:s, y:m, z:t | ( (x!=y and y!=z and x!=z) => x->y->z in (r))
}


pred galoish[r, m1, m2: univ->univ, s,t:univ]{
	all x:s, a:t | some y:s, b:t| ( x->a in r and x->y in m1 and a->b in m2 ) => y->b in r
}

pred tripleGaloish[r: univ->univ->univ, m1, m2: univ->univ, s,m,t:univ]{
	all x,y:s, a,b:t | some p,q:m | ( x->p->a in r and x->y in m1 and a->b in m2 ) => y->q->b in r
}


//Helper predcates for the ordered props. Changed over a copy from odering package.
/** return elements prior to e in the ordering */
fun prevs [e: univ, next:univ->univ ]: set univ { e.^(~(next)) }

/** return elements following e in the ordering */
fun nexts [e: univ, next:univ->univ]: set univ { e.^(next) }

/** e1 is less than e2 in the ordering */
pred lt [e1, e2: univ, next:univ->univ ] { e1 in prevs[e2, next] }

/** e1 is greater than e2 in the ordering */
pred gt [e1, e2: univ, next:univ->univ] { e1 in nexts[e2, next] }

/** e1 is less than or equal to e2 in the ordering */
pred lte [e1, e2: univ, next:univ->univ] { e1=e2 || lt [e1,e2, next] }

/** e1 is greater than or equal to e2 in the ordering */
pred gte [e1, e2: univ, next:univ->univ] { e1=e2 || gt [e1,e2, next] }
/** last */
fun last[elem: univ, next:univ->univ]: one univ { elem - (next.elem) }

fun max [es: set univ, next: univ->univ ]: lone univ { es - es.^(~(next)) }
fun min [es: set univ, next: univ->univ ]: lone univ { es - es.^(next) }

pred tripleNotEmptySets[s,m,t: univ]{
	some s
	some m
	some t
}

pred isFirstEmpty_s_t[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	no s_first.r
}


pred isGrowthFromEmpty_s_t_local_m[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{

	isFirstEmpty_s_t[r, s, m, t, s_first, s_next, t_first, t_next]
	isGrowth_s_t_local_m[r, s, m, t, s_first, s_next, t_first, t_next]
}

pred isGrowthStrictlyFromEmpty_s_t_local_m[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{

	isFirstEmpty_s_t[r, s, m, t, s_first, s_next, t_first, t_next]
	isGrowthStrictly_s_t_local_m[r, s, m, t, s_first, s_next, t_first, t_next]
}

//Growth
pred isGrowth_s_t_local_m[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	//tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next]| all b: m /*Make the middle one local*/ |  
		let a'= a.s_next | let c = b.(a.r) | let c' = b.(a'.r) |
			c in c'
}

pred isGrowth_s_t_global_m[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	//tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next]|/*Make the middle one local*/  
		let a'= a.s_next | let c = m.(a.r) | let c' = m.(a'.r) |
			c in c'
}

//Strictly Growth
pred isGrowthStrictly_s_t_local_m[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] |all b: m| /*Make the middle one local*/ 
		let a'= a.s_next | let c = b.(a.r) | let c' = b.(a'.r) |
			c in c' and (not c' in c ) 
}



//Strictly Growth
pred isGrowthStrictly_s_t_global_m[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | /*Make the middle one local*/ 
		let a'= a.s_next | let c = m.(a.r) | let c' = m.(a'.r) |
			c in c' and (not c' in c ) 
}


//Increase
pred isIncrease_s_t_local_m[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next]| all b: m /*Make the middle one local*/ |  
		let a'= a.s_next | let c = b.(a.r) | let c' = b.(a'.r) | let inc = c' - c |
			some inc => gte[min[inc, t_next], min[c, t_next], t_next]
}

//Strictly Increase
pred isIncreaseStrictly_s_t_local_m[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next]| all b: m /*Make the middle one local*/ |  
		let a'= a.s_next | let c = b.(a.r) | let c' = b.(a'.r) | let inc = c' - c |
			 (some inc) => lt[max[c,t_next],min[inc,t_next],t_next]
}













/**
* growth: if s_{i} < s_{i+1} => s_i.r in s_{i+1}.r and  s_{i+1}.r !in s_i.r
 **/
pred isTripleGrowthSingleton[r:univ->univ->univ, s, m, t: univ, 
								s_first: univ, s_next: univ->univ,
										s_i, s_i1: univ , b:m]{
	tripleNotEmptySets[s,m,t] =>
	s_i1 = s_next[s_i]
	(b.(s_i.r) in b.(s_i1.r)) and (	b.(s_i1.r) !in b.(s_i.r))
}

/**
* 
 **/
pred isTripleGrowthLocalMiddleSingleton[r:univ->univ->univ, s, m, t: univ, 
								s_first: univ, s_next: univ->univ,
										s_i, s_i1: univ ]{
	tripleNotEmptySets[s,m,t] =>
	all b: m | isTripleGrowthSingleton[r, s, m, t, s_first, s_next, s_i, s_i1, b ]
}

/**
* 
 **/
pred isTripleGrowthGlobalMiddleSingleton[r:univ->univ->univ, s, m, t: univ, 
								s_first: univ, s_next: univ->univ,
										s_i, s_i1: univ ]{
	tripleNotEmptySets[s,m,t] =>
	isTripleGrowthSingleton[r, s, m, t, s_first, s_next, s_i, s_i1, m ]
}

/**
* shrunk: if s_{i} < s_{i+1} => s_{i+1}.r in s_i.r and  s_i.r !in s_{i+1}.r
 **/
pred isTripleShrunkSingleton[r:univ->univ->univ, s, m, t: univ, 
								s_first: univ, s_next: univ->univ,
										s_i, s_i1: univ , b:m]{
	tripleNotEmptySets[s,m,t] =>
	s_i1 = s_next[s_i]
	(b.(s_i1.r) in b.(s_i.r)) and (b.(s_i.r) !in b.(s_i1.r))
}

/**
* 
 **/
pred isTripleShrunkLocalMiddleSingleton[r:univ->univ->univ, s, m, t: univ, 
								s_first: univ, s_next: univ->univ,
										s_i, s_i1: univ ]{
	tripleNotEmptySets[s,m,t] =>
	all b: m | isTripleShrunkSingleton[r, s, m, t, s_first, s_next, s_i, s_i1, b ]
}

/**
* 
 **/
pred isTripleShrunkGlobalMiddleSingleton[r:univ->univ->univ, s, m, t: univ, 
								s_first: univ, s_next: univ->univ,
										s_i, s_i1: univ ]{
	tripleNotEmptySets[s,m,t] =>
	isTripleShrunkSingleton[r, s, m, t, s_first, s_next, s_i, s_i1, m ]
}


/**
* nochange: if s_{i} < s_{i+1} => s_i.r = s_{i+1}.r 
 **/
pred isTripleNochangeSingleton[r:univ->univ->univ, s, m, t: univ, 
								s_first: univ, s_next: univ->univ,
										s_i, s_i1: univ , b:m]{
	tripleNotEmptySets[s,m,t] =>
	s_i1 = s_next[s_i]
	(b.(s_i.r) = b.(s_i1.r)) //and (b.(s_i1.r) in b.(s_i.r))
}

/**
* 
 **/
pred isTripleNochangeLocalMiddleSingleton[r:univ->univ->univ, s, m, t: univ, 
								s_first: univ, s_next: univ->univ,
										s_i, s_i1: univ ]{
	tripleNotEmptySets[s,m,t] =>
	all b: m | isTripleNochangeSingleton[r, s, m, t, s_first, s_next, s_i, s_i1, b ]
}

/**
* 
 **/
pred isTripleNochangeGlobalMiddleSingleton[r:univ->univ->univ, s, m, t: univ, 
								s_first: univ, s_next: univ->univ,
										s_i, s_i1: univ ]{
	tripleNotEmptySets[s,m,t] =>
	isTripleNochangeSingleton[r, s, m, t, s_first, s_next, s_i, s_i1, m ]
}


-----------------------Overal Growth
--Global
pred isTripleStrictlyGrowthOverallGlobalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleGrowthGlobalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}

pred isTripleGrowthOverallGlobalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | 
							isTripleGrowthGlobalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a'] || 
								isTripleNochangeGlobalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}

--Local
pred isTripleStrictlyGrowthOverallLocalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleGrowthLocalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}

pred isTripleGrowthOverallLocalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | 
							isTripleGrowthLocalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a'] || 
								isTripleNochangeLocalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}
--------------------Overal Shrunk
--Global
pred isTripleStrictlyShrunkOverallGlobalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleShrunkGlobalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}

pred isTripleShrunkOverallGlobalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | 
							isTripleShrunkGlobalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a'] || 
								isTripleNochangeGlobalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}

--Local
pred isTripleStrictlyShrunkOverallLocalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleShrunkLocalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}

pred isTripleShrunkOverallLocalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | 
							isTripleShrunkLocalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a'] || 
								isTripleNochangeLocalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}
---------------------No change
--Global
pred isTripleNochangeOverallGlobalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | 
								isTripleNochangeGlobalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}
--Local
pred isTripleNochangeOverallLocalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | 
								isTripleNochangeLocalMiddleSingleton[r, s, m, t, s_first, s_next, a,  a']
}

-------------------Empty Section

pred isTripleEmptyStart[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{

	--tripleNotEmptySets[s,m,t] =>
	no s_first.r
}

-------------------Start from empty
--Global
pred isTripleStrictlyGrowthOverallFromEmptyGlobalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleStrictlyGrowthOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleGrowthOverallFromEmptyGlobalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleGrowthOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}


pred isTripleStrictlyShrunkOverallFromEmptyGlobalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleStrictlyShrunkOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleShrunkOverallGlobalFromEmptyMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleShrunkOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleNochangeOverallFromEmptyGlobalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleNochangeOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

--Local
pred isTripleStrictlyGrowthOverallFromEmptyLocalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleStrictlyGrowthOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleGrowthOverallFromEmptyLocalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleGrowthOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}


pred isTripleStrictlyShrunkOverallFromEmptyLocalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleStrictlyShrunkOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleShrunkOverallLocalFromEmptyMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleShrunkOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleNochangeOverallFromEmptyLocalMiddleSinglton[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ]{
	isTripleEmptyStart[r,s,m,t,s_first,s_next]
	isTripleNochangeOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}



//The following three pred are the wrappers to make the experiment easier.

----------------------Global
pred isTripleStrictlyGrowthOverallGlobalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleStrictlyGrowthOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleGrowthOverallGlobalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleGrowthOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleStrictlyShrunkOverallGlobalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleStrictlyShrunkOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleShrunkOverallGlobalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleShrunkOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}


pred isTripleNochangeOverallGlobalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleNochangeOverallGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleStrictlyGrowthOverallFromEmptyGlobalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleStrictlyGrowthOverallFromEmptyGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleGrowthOverallFromEMPTYGlobalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleGrowthOverallFromEmptyGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}


pred isTripleStrictlyShrunkOverallFromEmptyGlobalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleStrictlyShrunkOverallFromEmptyGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleShrunkOverallGlobalFromEMPTYMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleShrunkOverallGlobalFromEmptyMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleNochangeOverallFromEMPTYGlobalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleNochangeOverallFromEmptyGlobalMiddleSinglton[r, s, m, t, s_first, s_next]
}

---------------------Local

----------------------Global
pred isTripleStrictlyGrowthOverallLocalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleStrictlyGrowthOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleGrowthOverallLocalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleGrowthOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleStrictlyShrunkOverallLocalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleStrictlyShrunkOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleShrunkOverallLocalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleShrunkOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}


pred isTripleNochangeOverallLocalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleNochangeOverallLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleStrictlyGrowthOverallFromEmptyLocalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleStrictlyGrowthOverallFromEmptyLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleGrowthOverallFromEMPTYLocalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleGrowthOverallFromEmptyLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}


pred isTripleStrictlyShrunkOverallFromEmptyLocalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleStrictlyShrunkOverallFromEmptyLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleShrunkOverallLocalFromEMPTYMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleShrunkOverallLocalFromEmptyMiddleSinglton[r, s, m, t, s_first, s_next]
}

pred isTripleNochangeOverallFromEMPTYLocalMiddleSingltonTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleNochangeOverallFromEmptyLocalMiddleSinglton[r, s, m, t, s_first, s_next]
}

-------------------


pred isTripleEmptyStartTMP[r:univ->univ->univ, s, m, t: univ, 
														s_first: univ, s_next: univ->univ,
															t_first: univ, t_next: univ->univ]{
	isTripleEmptyStart[r, s, m, t, s_first, s_next]
}






----------------Relation between orders

//Increase strictly between two states, if there is growth
pred isTripleIncreaseIfGrowthStrict[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
						s_i,s_i1: univ, b: univ]{
	tripleNotEmptySets[s,m,t] =>
	
	let c = b.(s_i.r) | let c' = b.(s_i1.r) | let inc = c' - c |
		some inc => lt[max[c,t_next],min[inc,t_next],t_next]
}

pred isTripleIncreaseIfGrowthStrictLocalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
							s_i,s_i1: univ]{
	tripleNotEmptySets[s,m,t] =>
	all b: m | isTripleIncreaseIfGrowthStrict[r, s, m, t, s_first, s_next, t_first, t_next, s_i, s_i1, b]
}

pred isTripleIncreaseIfGrowthStrictGlobalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
							s_i,s_i1: univ]{
	tripleNotEmptySets[s,m,t] =>
	isTripleIncreaseIfGrowthStrict[r, s, m, t, s_first, s_next, t_first, t_next, s_i, s_i1, m]
}


pred isTripleIncreaseIfGrowthStrictOverallLocalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleIncreaseIfGrowthStrictLocalMiddle[r, s, m, t, s_first, s_next, t_first, t_next, a, a']
}

pred isTripleIncreaseIfGrowthStrictOverallGlobalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleIncreaseIfGrowthStrictGlobalMiddle[r, s, m, t, s_first, s_next, t_first, t_next, a, a']
}


//IncreaseIfGrowth loosely between two states, if there is growth
pred isTripleIncreaseIfGrowth[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
						s_i,s_i1: univ, b: univ]{
	tripleNotEmptySets[s,m,t] =>
	let c = b.(s_i.r) | let c' = b.(s_i1.r) | let inc = c' - c |
		some inc => lte[min[c, t_next], min[inc, t_next],  t_next]
//		some inc => gte[min[inc, t_next], min[c, t_next], t_next]
}

pred isTripleIncreaseIfGrowthLocalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
							s_i,s_i1: univ]{
	tripleNotEmptySets[s,m,t] =>
	all b: m | isTripleIncreaseIfGrowth[r, s, m, t, s_first, s_next, t_first, t_next, s_i, s_i1, b]
}

pred isTripleIncreaseIfGrowthGlobalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
							s_i,s_i1: univ]{
	tripleNotEmptySets[s,m,t] =>
	isTripleIncreaseIfGrowth[r, s, m, t, s_first, s_next, t_first, t_next, s_i, s_i1, m]
}


pred isTripleIncreaseIfGrowthOverallLocalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleIncreaseIfGrowthLocalMiddle[r, s, m, t, s_first, s_next, t_first, t_next, a, a']
}

pred isTripleIncreaseIfGrowthOverallGlobalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleIncreaseIfGrowthGlobalMiddle[r, s, m, t, s_first, s_next, t_first, t_next, a, a']
}


---------------------------------------------------------------
//decrease if growth
pred isTripleDecreaseIfGrowthStrict[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
						s_i,s_i1: univ, b: univ]{
	tripleNotEmptySets[s,m,t] =>
	let c = b.(s_i.r) | let c' = b.(s_i1.r) | let inc = c' - c |
		some inc => gt[min[c,t_next],max[inc,t_next],t_next]
}

pred isTripleDecreaseIfGrowthStrictLocalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
							s_i,s_i1: univ]{
	tripleNotEmptySets[s,m,t] =>
	all b: m | isTripleDecreaseIfGrowthStrict[r, s, m, t, s_first, s_next, t_first, t_next, s_i, s_i1, b]
}

pred isTripleDecreaseIfGrowthStrictGlobalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
							s_i,s_i1: univ]{
	tripleNotEmptySets[s,m,t] =>
	isTripleDecreaseIfGrowthStrict[r, s, m, t, s_first, s_next, t_first, t_next, s_i, s_i1, m]
}

pred isTripleDecreaseIfGrowthStrictOverallLocalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleDecreaseIfGrowthStrictLocalMiddle[r, s, m, t, s_first, s_next, t_first, t_next, a, a']
}

pred isTripleDecreaseIfGrowthStrictOverallGlobalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleDecreaseIfGrowthStrictGlobalMiddle[r, s, m, t, s_first, s_next, t_first, t_next, a, a']
}


//DecreaseIfGrowth loosely between two states, if there is growth
pred isTripleDecreaseIfGrowth[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
						s_i,s_i1: univ, b: univ]{
	tripleNotEmptySets[s,m,t] =>
	let c = b.(s_i.r) | let c' = b.(s_i1.r) | let inc = c' - c |
		some inc => lte[max[inc, t_next], max[c, t_next], t_next]
}

pred isTripleDecreaseIfGrowthLocalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
							s_i,s_i1: univ]{
	tripleNotEmptySets[s,m,t] =>
	all b: m | isTripleDecreaseIfGrowth[r, s, m, t, s_first, s_next, t_first, t_next, s_i, s_i1, b]
}

pred isTripleDecreaseIfGrowthGlobalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ,
							s_i,s_i1: univ]{
	tripleNotEmptySets[s,m,t] =>
	isTripleDecreaseIfGrowth[r, s, m, t, s_first, s_next, t_first, t_next, s_i, s_i1, m]
}


pred isTripleDecreaseIfGrowthOverallLocalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleDecreaseIfGrowthLocalMiddle[r, s, m, t, s_first, s_next, t_first, t_next, a, a']
}

pred isTripleDecreaseIfGrowthOverallGlobalMiddle[r:univ->univ->univ, s, m, t: univ, 
					s_first: univ, s_next: univ->univ,
						t_first: univ, t_next: univ->univ]{
	tripleNotEmptySets[s,m,t] =>
	all a: s - last[s, s_next] | let a'= a.s_next | isTripleDecreaseIfGrowthGlobalMiddle[r, s, m, t, s_first, s_next, t_first, t_next, a, a']
}


------------------------------------------------
//increase if shrink


//decrease if shrink



//TBD
pred isTripleGrowthBinary[]{
}



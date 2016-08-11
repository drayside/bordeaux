module relational_properties_tagged

/*
 * Utilities for some common operations and constraints
 * on binary relations. The keyword 'univ' represents the
 * top-level type, which all other types implicitly extend.
 * Therefore, all the functions and predicates in this model
 * may be applied to binary relations of any type.
 *
 * author: Greg Dennis
 */

pred noop[r:univ->univ]{
}

pred notempty[r:univ->univ]{
	not empty[r]
}

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
pred total [r: univ->univ, left: set univ] {
  all x: left | some x.r
}

/** r is a partial function over the domain s */
pred functional [r: univ->univ, left: set univ] {
  all x: left | lone x.r
}

/** r is a total function over the domain s */
pred function [r: univ->univ, left: set univ] {
  all x: left | one x.r
}

///////? it used to be s and I made it to t.
/** r is surjective over the codomain s or range*/
pred surjective [r: univ->univ, right: set univ] {
  all x: right | some r.x
}


///////? it used to be s and I made it to t.
/** r is injective */
pred injective [r: univ->univ, right: set univ] {
  all x: right | lone r.x
}

/** equivalent to defining r = set A -> one B -> set C*/
pred innerinjective [ r :univ->univ->univ ]{
  all x:r.univ.univ | injective[x.r, univ.(x.r)]
}

///////? it used to be s and I made it to t.
/** r is bijective over the codomain s */
pred bijective[r: univ->univ, right: set univ] {
  all x: right | one r.x
}

/** r is a bijection over the domain d and the codomain c */
pred bijection[r: univ->univ, left, right: set univ] {
  function[r, left] && bijective[r, right]
}

//Does it make any sense to have refexive property where domaind and range are different?
/** r is reflexive over the set s */
pred reflexive [r: univ -> univ, left: set univ] {
left<:iden in r
}

--Same as previous
/** r is irreflexive */
pred irreflexive [r: univ -> univ, left,right:univ] {
left = right
no iden & r
}

--Same as previous
/** r is symmetric */
pred symmetric [r: univ -> univ, left,right: univ] {
left = right
~r in r
}

--Same as previous
/** r is anti-symmetric */
pred antisymmetric [r: univ -> univ, left,right: univ] {
left = right
~r & r in iden}

--Same as previous
/** r is transitive */
pred transitive [r: univ -> univ, left,right: univ] {
left = right
r.r in r}

//Not sure wether it makes sences. But if the type of domain and range are different, then
//the relation `r` is absloutly acyclic.
/** r is acyclic over the set s */
pred acyclic[r: univ->univ, left: set univ] {
  all x: left | x !in x.^r
}


/** r is complete over the set s */
/*pred complete[r: univ->univ, s: univ] {
  all x,y:s | (x!=y => x->y in (r + ~r))
}*/
//compelte and complete2 are equivalent, if domain and range come from the same set.
pred complete[r: univ->univ, left: univ, right:univ] {
  all x:left, y:right | (x!=y => x->y in (r + ~r))
}

//Same as reflexive
/** r is a preorder (or a quasi-order) over the set s */
pred preorder [r: univ -> univ, left,right: set univ] {
  reflexive[r, left]
  transitive[r, left, right]
}

//Same as reflexive
/** r is an equivalence relation over the set s */
pred equivalence [r: univ->univ, left, right: set univ] {
  preorder[r, left, right]
  symmetric[r, left, right]
}

//Same as reflexive
/** r is a partial order over the set s */
pred partialOrder [r: univ -> univ, left, right: set univ] {
  preorder[r, left, right]
  antisymmetric[r, left, right]
}

//Same as reflexive, although there is a `complete` property in the a total order,
//but since `partialOrder` takes a set, then `totalOrder` is defined over a set.
/** r is a total order over the set s */
pred totalOrder [r: univ -> univ, left, right: set univ] {
  partialOrder[r, left, right]
  complete[r, left, right]
}

/**rootedAll: all elements in domain can reach all elements in range*/
/*pred rootedAll [r: univ->univ, t: univ]{
  all root:t | t in root.*r
}*/
//rootedAll2 can be replaced with rootedAll when both s and t are equal.
pred rootedAll [r: univ->univ, left:univ, right: univ]{
  all root:left | right in root.*r
}

/**rootedOne: one element in domain can reach all elements in range*/
/*pred rootedOne [r: univ->univ, t: univ]{
  one root:t | t in root.*r
}*/
pred rootedOne [r: univ->univ, left:univ, right: univ]{
  one root:left | right in root.*r
}

/**stronglyConnected: all elements in domain can reach all elements in range */
/*pred stronglyConnected [ r :univ->univ , t :univ ] {
  all disj d,g: t | d in g.^r
}*/
pred stronglyConnected [ r :univ->univ, left:univ, right:univ ] {
  all d: right | all g: left - d | d in g.^r
}

/**weaklyConnected: all elements in domain reach or are reachable by all elements in range */
/*pred weaklyConnected [ r :univ->univ , t :univ ] {
  all disj d,g: t | d in g.^(r + ~r)
}*/
pred weaklyConnected [ r :univ->univ,  left:univ, right:univ ] {
  all d: right | all g: left - d  | d in g.^(r + ~r)
}

pred tripleSameType[left,middle,right:univ]{
	left = middle
	left = right
	middle = right
}

----------------------Ternary relations
pred antisymmetric3 [ r :univ->univ->univ, left,middle,right:univ ] {
	//Type of x->y->z has to be the same as z->y->x
	tripleSameType[left,middle,right]
	all x,y,z: univ | x->y->z in r => z->y->x !in r
}

pred cyclic [ r :univ->univ->univ, left,middle,right:univ ] {
	tripleSameType[left,middle,right]
	all x,y,z: univ | (x->y->z in r) => (y->z->x in r)
}

pred irreflexive3 [ r :univ->univ ->univ, left,middle,right:univ] {
	tripleSameType[left, middle, right]
	no x:univ | x->x->x in  r
}

pred irreversible [ r :univ->univ ->univ, left,middle,right:univ] {
	tripleSameType[left,middle,right]
	(all x,y,z,u:univ| x->y->z in r  => y->x->u !in r) 
}

pred regular [ r :univ->univ ->univ, left,middle,right:univ ] {
	tripleSameType[left, middle,right]
	weaklyRegular[r, left, middle, right]
	all x,y,z,p,q:univ| x->y->p in r and x->z->q in r => x->y->z in r
}

//undirectional ternary relations
pred symmetric3 [ r :univ->univ ->univ, left,middle,right:univ ] {
	tripleSameType[left, middle, right]
	all x,y,z: univ | x->y->z in r => z->y->x in r
}

pred transitive3 [ r :univ->univ->univ, left,middle,right:univ ] { 
	tripleSameType[left, middle, right]
	(all x,y,z,u:univ| x->y->z in r and z->y->u in r => x->y->u in r) 
}

pred translative[ r :univ->univ->univ, left,middle,right:univ ] {
	tripleSameType[left, middle, right] 
	weaklyRegular[r, left, middle, right]
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

pred weaklyTransitive [ r :univ->univ->univ, left,middle,right:univ ] { 
	tripleSameType[left, middle, right]
	(all x,y,u:univ| x->y->y in r and y->y->u in r => x->y->u in r) 
}

pred weaklyRegular[ r :univ->univ->univ, left,middle,right:univ ] { 
	tripleSameType[left, middle, right]
	(all x,y,z,p,q:univ| x->y->p in r and y->z->q in r => x->y->z in r) 
}

pred weaklyTranslative[ r :univ->univ->univ, left,middle,right:univ ] { 
	tripleSameType[left, middle, right]
	all x,y,z,p,q:univ| x->y->z in r and y->p->q in r => some u:univ| x->p->u in r
}


-----------------------------------
/**
*	In the following properties, the relation is ternary and defined as r:s->m->t
**/
//one s
pred oneDom[r:univ->univ->univ, middle,right:univ ]{
	one (r.right).middle
}

//one m
pred oneMiddle[r:univ->univ->univ, left,right:univ ]{
	one left.(r.right)
}

//one t
pred oneRange[r:univ->univ->univ, left,middle:univ ]{
	one middle.(left.r)
}

//tripple functional. for every x in domain, there is pair in t.
pred tripleTotal [r:univ->univ->univ, left:univ ] {
  all x: left | some x.r
}

/** r is a partial function over the domain s */
pred tripleFunctional [r:univ->univ->univ, left:univ] {
  all x: left | lone x.r
}

/** r is a total function over the domain s */
pred tripleFunction [r: univ->univ->univ, left,middle:univ] {
  all x: left | one middle.(x.r)
}

pred tripleSurjective [r:univ->univ->univ, middle,right:univ ] {
  all x: right | some (r.x).middle
}


///////? it used to be s and I made it to t.
/** r is injective */
pred tripleInjective [r: univ->univ->univ, middle,right:univ ] {
  all x: right | lone (r.x).middle
}

///////? it used to be s and I made it to t.
/** r is bijective over the codomain s */
pred tripleBijective[r: univ->univ->univ, middle, right:univ ] {
  all x: right | one (r.x).middle
}

/** r is a bijection over the domain d and the codomain c */
pred tripleBijection[r: univ->univ->univ, left,middle,right:univ ] {
  tripleFunction[r, left,middle] and tripleBijective[r, middle, right]
}

pred noDiamond [r:univ->univ->univ, left,middle,right:univ] {
	all x:left, disj y,w:middle, z:left | x->y->z in r => x->w->z ! in r
}



//rootedAll2 can be replaced with rootedAll when both s and t are equal.
pred tripleSourcesAll [r: univ->univ->univ, left,middle,right:univ]{
  all root:left | right in middle.(root.r)
}

/**rootedOne: one element in domain can reach all elements in range*/
/*pred rootedOne [r: univ->univ, t: univ]{
  one root:t | t in root.*r
}*/
pred tripleRootedOne [r: univ->univ->univ, left,middle,right:univ]{
  one root:left | right in middle.(root.r)
}
//is this a forest. do we have a single tree an all other nodes from s does not go anywhere.

/**stronglyConnected: all elements in domain can reach all elements in range */
/*pred stronglyConnected [ r :univ->univ , t :univ ] {
  all disj d,g: t | d in g.^r
}*/
pred tripleStronglyConnected [ r :univ->univ->univ, left,middle,right:univ] {
  all a:left, b:middle, c:right | a->b->c in r
}


pred tripleComplete[r: univ->univ->univ, left,middle,right:univ] {
  all x:left, y:middle, z:right | ( (x!=y and y!=z and x!=z) => x->y->z in (r))
}


pred galoish[r, m1, m2: univ->univ, left,right:univ]{
	all x:left, a:right | some y:left, b:right| ( x->a in r and x->y in m1 and a->b in m2 ) => y->b in r
}

pred tripleGaloish[r: univ->univ->univ, m1, m2: univ->univ,  left,middle,right:univ]{
	all x,y:left, a,b:right | some p,q:middle | ( x->p->a in r and x->y in m1 and a->b in m2 ) => y->q->b in r
}


//Helper predcates for the ordered props. Changed over a copy from odering package.
/** return elements prior to e in the ordering */
fun prevs [e: univ, next:univ->univ ]: set univ { e.^(~(next)) }

/** return elements following e in the ordering */
fun nexts [e: univ, next:univ->univ]: set univ { e.^(next) }

/** e1 is less than e2 in the ordering */
pred lt [e1, e2: univ, next:univ->univ ] { e1 in this/prevs[e2, next] }

/** e1 is greater than e2 in the ordering */
pred gt [e1, e2: univ, next:univ->univ] { e1 in this/nexts[e2, next] }

/** e1 is less than or equal to e2 in the ordering */
pred lte [e1, e2: univ, next:univ->univ] { e1=e2 || lt [e1,e2, next] }

/** e1 is greater than or equal to e2 in the ordering */
pred gte [e1, e2: univ, next:univ->univ] { e1=e2 || gt [e1,e2, next] }
/** last */
fun last[elem: univ, next:univ->univ]: one univ { elem - (next.elem) }

fun max [es: set univ, next: univ->univ ]: lone univ { es - es.^(~(next)) }
fun min [es: set univ, next: univ->univ ]: lone univ { es - es.^(next) }

pred tripleNotEmptySets[left, middle, right :univ]{
	some left
	some middle
	some right
}

run {}

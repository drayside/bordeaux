
abstract sig Value {}
one sig dense, sparse, list_ds, array_ds, list_alg, array_alg, other extends Value {}


abstract sig Variable {
} {
	-- [NEW] a variable has more than one value to choose from
	not lone domain
}
one sig Matrix, Ds, Alg extends Variable {}

fun domain[] : Variable->Value {
	Matrix->(dense+sparse) + Ds->(list_ds+array_ds+other) + Alg->(array_alg + list_alg + other)
}


fact {
	-- there are no Variable and Value that aren't bound to some "concrete" atom 
	-- (important: otherwise solution generation might fail)
	Value = dense + sparse + list_ds + array_ds +  list_alg + array_alg + other 
	Variable = Matrix + Ds + Alg
}

one sig B_Matrix_dense, B_Matrix_sparse, B_Ds_list_ds, B_Ds_array_ds, B_Ds_other, B_Alg_array_alg, B_Alg_list_alg, B_Alg_other extends Binding {}

fun var[] : Binding->Variable { 
	B_Matrix_dense->Matrix + 
	B_Matrix_sparse->Matrix + 
	B_Ds_list_ds->Ds + 
	B_Ds_array_ds->Ds + 
	B_Ds_other->Ds + 
	B_Alg_array_alg->Alg + 
	B_Alg_list_alg->Alg + 
	B_Alg_other->Alg 
}

fun val[] : Binding->Value { 
	B_Matrix_dense->dense + 
	B_Matrix_sparse->sparse + 
	B_Ds_list_ds->list_ds + 
	B_Ds_array_ds->array_ds + 
	B_Ds_other->other + 
	B_Alg_array_alg->array_alg + 
	B_Alg_list_alg->list_alg + 
	B_Alg_other->other
}

sig Binding {
//	var : one Variable,
//	val : one Value
} {
	-- [7.1.1] a variable can only be bound to one of its legal values
	val in var.domain
}


abstract sig Assignment {
	bindings: set Binding
} 

abstract sig TotalAssignment extends Assignment {} {
	bindings.var = Variable
	all b1 : bindings | no b2 : bindings | b1 != b2 and b1.var = b2.var
}

sig PartialAssignment extends Assignment {}



sig Solution in TotalAssignment {}
sig State = Solution {}


sig Transition {
	from: one State,
	forced: one Variable, -- the variable in which a change was forced by some external factor
	compensating: set Variable, -- variables that changed to compensate for the forced change
	letter: one PartialAssignment, -- [7.1.9] the change between from and to 
//By V: According p101 of thesis: The alphabet of a DA is a set of variable-value pairs
	to: one State, 
}{
	letter.bindings = to.bindings - ( from.bindings & to.bindings )
}


-- [7.1.17] transitions are minimal
-- note: this fact prohibits to generate instances with 3 solutions that have no transition (because of some) 
/*fact MinimalTransitions {
	all disjoint s1, s2, s3 : Solution | {
		some t1 : Transition | s1 = t1.from and s2 = t1.to
		=> 
		no t2 : Transition | s1 = t2.from and s3 = t2.to and 
				(t2.letter).bindings in (t1.letter).bindings
	}
}
*/
pred EqualsTransitions[ t1, t2 : Transition ] {
	t1.from = t2.from
	t1.forced = t2.forced
	t1.compensating = t2.compensating
	t1.letter = t2.letter
	t1.to = t2.to
}

pred IsomorphicTransitions[ t1, t2 : Transition ] {
	t1.from = t2.from
	t1.letter = t2.letter
	t1.to = t2.to
}

pred LegalTransition[ t : Transition ] {
	-- [NEW] no self-transitions
	t.from != t.to
	-- [7.1.16] the letter is compatible with the target state
	t.letter.bindings in t.to.bindings
	-- [NEW] the letter is compatable with the source state
	(t.to.bindings - t.letter.bindings) in t.from.bindings
	no t.letter.bindings & t.from.bindings
	-- [NEW] forced and letter are compatible
	t.forced in ((t.letter).bindings).var
	-- [NEW] define compensating
	t.compensating = (t.letter.bindings).var - t.forced
	-- every Transition is a legal part of some DesignAutomaton
	let da = transitions.t | {
		-- transition is part of a design automaton
		some da
		-- and if the transition has compensating variables,
		-- those respect the dominance (7.1.18)
		some (t.forced -> t.compensating) =>
		(t.forced -> t.compensating) not in da.acn.dominates 
	}
}

pred LegalTransitionPossible[ da : DesignAutomaton, s1, s2 : State, v : Variable ] {
	-- make sure we have disjoint singletons here
	one da and one s1 and one s2
	-- the two states are different ones
	s1 != s2
	-- both are states in the same DA
	(s1+s2) in da.states
	-- the forced variable v differs in the two states
	some b1 : s1.bindings | b1.var = v and some b2 : s2.bindings |
		b2.var = v and b1.val != b2.val
	-- if there are variables which compensate for v,
	-- then all these variables repect the domiance relation 
	let comp = ((s2.bindings - (s2.bindings & s1.bindings)).var - v) |
		some comp => not  ((v->comp) in da.acn.dominates)
}




sig AugmentedConstraintNetwork {
	-- the user provides the dominance relation as an input
} {
	-- [NEW] no self-loops in the dominates relation
	all v: Variable | (v->v) not in this.dominates
}

fun dominates[] : AugmentedConstraintNetwork->Variable->Variable {
	AugmentedConstraintNetwork -> ((Ds->Matrix) + (Alg->Matrix))
}
fun solutions[] : AugmentedConstraintNetwork->Solution {
	AugmentedConstraintNetwork -> Solution
}

sig DesignAutomaton {
	acn : one AugmentedConstraintNetwork,
	transitions : set Transition,
}
fun states[] : DesignAutomaton -> State {
	acn.solutions
}
fact NoUnassociatedStates {
	all s : State | some da : DesignAutomaton | s in da.states
}


-- [7.1.19 + 7.1.20] compute PWDR
pred depends[ x, y : Variable ] {
	some t : Transition | x in t.forced and y in t.compensating
}
fun depends[] : Variable -> Variable {
	{ x, y : Variable | depends[x,y] }
}

fun bindings[s : set Binding] : Variable->Value {
	{ vr : Variable, vl : Value | some b : s | b.var = vr and b.val = vl }
}










/******* Matrix Design Space *********/
/*
bounds MatrixBounds {
	3,
	exactly 1 AugmentedConstraintNetwork,
	exactly 1 DesignAutomaton,
	Value = dense + sparse + list_ds + array_ds + list_alg + array_alg + other,
	Variable = Matrix + Ds + Alg,
	domain = Matrix->(dense+sparse) + Ds->(list_ds+array_ds+other) + Alg->(array_alg + list_alg + other),
	dominates = AugmentedConstraintNetwork -> ((Ds->Matrix) + (Alg->Matrix)),
	solutions = AugmentedConstraintNetwork -> Solution,
	generate b : Binding | b.val in b.var.domain
	generate a : TotalAssignment | ...
	generate t : Transition | LegalTransition[t]
}
run createMatrixACN for MatrixBounds
*/


/*** constraints ***/

pred createMatrixACN {
	-- a set of bindings is a valid CN solution iff there is a solution for this set 
	all disjoint b1, b2, b3: Binding | let bs = {b1 + b2 + b3} | 
		 isValidCNSolution[bs] <=> {some a: Solution | a.bindings = bs}
}

pred isValidCNSolution[bs: set Binding]{
	-- set of Bindings respects all constraints
	nr4[bs] and nr5[bs] and nr6[bs] and nr7[bs] and nrXX[bs]
	-- each variable is only once in the set
	all b: bs | no b2 : bs | b != b2 and b.var = b2.var
	-- the set talks about all variables
	all v: Variable | some b:bs | b.var = v
}



/*** end of generator ***/



/* ds = array_ds => matrix = dense */
pred nr4[bs: set Binding] {
		(some  ds: Binding | ds in bs and ds.var = Ds and ds.val = array_ds)
		=>
		(some matrix: Binding |  matrix in bs and  matrix.var = Matrix and matrix.val = dense)

}

/* ds = list_ds => matrix = sparse */
pred nr5[bs: set Binding]  {
		(some  ds: Binding | ds in bs and ds.var = Ds and ds.val = list_ds)
		=>
		(some matrix: Binding |  matrix in bs and  matrix.var = Matrix and matrix.val = sparse)
}

/* alg = array_alg => ds = array_ds */
pred nr6[bs: set Binding]{
		(some alg: Binding | alg in bs and alg.var = Alg and alg.val = array_alg)
		=>
		(some ds: Binding |  ds in bs and  ds.var = Ds and ds.val = array_ds)
}

/* alg = list_alg => ds = list_ds */
pred nr7[bs: set Binding] {
		(some alg: Binding | alg in bs and alg.var = Alg and alg.val = list_alg)
		=>
		(some ds: Binding |  ds in bs and  ds.var = Ds and ds.val = list_ds)
}

/* testing: alg = other && ds = other */
pred nrXX[bs: set Binding]{
		some alg: Binding | alg in bs and alg.var = Alg and alg.val = other
//		some ds: Binding |  ds in bs and  ds.var = Ds and ds.val = other
}


pred EqualBinding[b1, b2 : Binding] {
	b1.var = b2.var
	b1.val = b2.val
}

pred generateBindings[] {
	-- canonical
	all disjoint b1, b2 : Binding | not EqualBinding[b1, b2]
//	-- generator
//	all r : Variable | all l : r.domain | some b : Binding | b.var = r and b.val = l
}


fact CanonicalizeTotalAssignments {
	all disjoint a1, a2 : TotalAssignment | a1.bindings != a2.bindings
}
--The older name was createPossibleCNSolution.
pred generateSolutions {
	generateBindings
	-- a set of bindings is a valid CN solution iff there is a solution for this set 
	all disjoint b1, b2, b3: Binding | let bs = {b1 + b2 + b3} | 
	--The Solution has been replazed by TotalAssignment. It was not clear for me yet that why the Solution was an empty set.
		 isValidCNSolution[bs] <=> {some a: Solution | a.bindings = bs}
}

fact TransitionIsLegal {
	-- each transition is legel, i.e. it respects certain criteria
	all t: Transition | LegalTransition[t]
}

fact CanonicalizeTransitions {
		no disjoint t1, t2 : Transition | EqualsTransitions[t1,t2]
}
-- [7.1.17] transitions are minimal
-- note: this fact prohibits to generate instances with 3 solutions that have no transition (because of some) 
fact MinimalTransitions {
	all disjoint s1, s2, s3 : Solution | {
		some t1 : Transition | s1 = t1.from and s2 = t1.to
		=> 
		no t2 : Transition | s1 = t2.from and s3 = t2.to and 
				(t2.letter).bindings in (t1.letter).bindings
	}
}

fact AllAvailableTransitionsIncorporated {
	all t : Transition | all da : DesignAutomaton | { (t.from + t.to) in da.states => t in da.transitions }
}

pred TransitionGenerator {
	generateSolutions
	all da : DesignAutomaton | all s1, s2 : da.states, v: Variable | 
		LegalTransitionPossible[da, s1,s2, v] => some t : Transition | t.from = s1 and t.to = s2 and t.forced = v
}



run TransitionGenerator for 15 but 
exactly 1 DesignAutomaton, 
exactly 4 TotalAssignment,
exactly 3 Variable,
exactly 12 Transition

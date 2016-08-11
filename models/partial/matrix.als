/*
open util/ordering[Binding]
open util/ordering[Assignment]
open util/ordering[Value]

open util/ordering[Variable]
*/

-- [7.1.2] simplified away
-- [7.1.3] simplified away
-- [7.1.4] choose to not model: FDCN solving is well understood   (Why?)
-- [7.1.5] choose to not model: FDCN solving is well understood
-- [7.1.6] simplified away
-- [7.1.7] simplified away
-- [7.1.8] simplified away
-- [7.1.11] simplified away
-- [7.1.12] simplified away
-- [7.1.13] simplified away
-- [7.1.14] simplified away
-- [7.1.15] simplified away


abstract sig Value {}
//one sig dense, sparse, list_ds, array_ds, list_alg, array_alg, other {}

abstract sig Variable {
	domain: set Value,
} {
//	not lone domain
}

pred predicateName{}

/*fact {
	Value = dense + sparse + list_ds + array_ds +  list_alg + array_alg + other 
	Variable = Matrix + Ds + Alg
}*/




/******* Matrix Design Space *********/

inst BoundsName {
 	4,
//	exactly 1 Value,
	 Variable = a + b + c//,
	,Value = z + x + y + w 
 
	,domain in a->z + a->x + c->x + b->z + b->x  //+c->z
/*+ list_ds + array_ds + list_alg + array_alg + other/*,
	exactly 2 Binding,
	exactly 4 Assignment,
	exactly 3 Transition,
	exactly 1 AugmentedConstraintNetwork,
exactly 1 DesignAutomaton*/}/*,
	Value = dense + sparse + list_ds + array_ds + list_alg + array_alg + other,
	Variable = Matrix + Ds + Alg,
	domain = Matrix->(dense+sparse) + Ds->(list_ds+array_ds+other) + Alg->(array_alg + list_alg + other),

	dominates = AugmentedConstraintNetwork -> ((Ds->Matrix) + (Alg->Matrix)),
	solutions = AugmentedConstraintNetwork -> Solution
}/*	generate b : Binding | b.val in b.var.domain
	generate a : TotalAssignment | ...
	generate t : Transition | LegalTransition[t]
}*/
run predicateName for BoundsName


abstract sig Value {}
//one sig dense, sparse, list_ds, array_ds, list_alg, array_alg, other extends Value {}

abstract sig Variable {
	domain: set Value,
} 


sig Binding {
	var : one Variable,
	val : one Value
} {
	-- [7.1.1] a variable can only be bound to one of its legal values
	val in var.domain
}



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


pred EqualBinding[b1, b2 : Binding] {
	b1.var = b2.var
	b1.val = b2.val
}

pred generateBindings[] {
	-- canonical
	all disjoint b1, b2 : Binding | not EqualBinding[b1, b2]
	-- generator
	all r : Variable | all l : r.domain | some b : Binding | b.var = r and b.val = l
	some b: Binding | b.val = array_ds
}


//run generateBindings for 0 but 
//	21 Binding -- how do we know that we need 8?

/******* Matrix Design Space *********/

inst MatrixBounds {
	3,
	exactly 8 Binding,
	Value = dense + sparse + list_ds + array_ds + list_alg + array_alg + other_alg + other_ds,
	Variable = Matrix + Ds + Alg,
	domain = Matrix->dense+ Matrix->sparse + 
					Ds->list_ds+ Ds->array_ds+Ds->other_ds + 
					Alg->array_alg + Alg->list_alg + Alg->other_alg
/*//	dominates = AugmentedConstraintNetwork -> ((Ds->Matrix) + (Alg->Matrix)),
	solutions = AugmentedConstraintNetwork -> Solution,
	generate b : Binding | b.val in b.var.domain
	generate a : TotalAssignment | ...
	generate t : Transition | LegalTransition[t]*/
}{dense, sparse, list_ds, array_ds, list_alg, array_alg, other_alg, other_ds, Matrix, Ds, Alg}
run generateBindings for MatrixBounds



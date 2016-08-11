open binary_implication

/**
* This model returns a source in the implication lattice at 
* each SAT-CAll. 
**/

pred run_getSourcesImplication[]{
	some p: prop | getSourcesImplication[p]
}

pred run_getAllImplied2[p: prop]{
	some p': prop | getAllImplied[p,p']
}

run {run_getAllImplied2[rootedAll]} for 0

/*pred run_getAllImplied[p: prop]{
	getAllImplied[p]
}

run {run_getAllImplied[reflexive]} for 0

pred run_getAllRevImplied[p: prop]{
	getAllRevImplied[p]
}

run {run_getAllRevImplied[reflexive]} for 0*/

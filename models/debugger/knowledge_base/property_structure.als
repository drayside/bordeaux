module property_structure

abstract sig prop{imply: set prop, inconst: set prop}{
	no inconst
}

fact {
	all p,p': prop | p->p' in inconst implies p'->p in inconst
}

pred getSourcesImplication[p: prop]{
	no imply.p
}

pred getNextImplications[p,p': prop]{
	p' in p.imply
}

pred getFinalSinksImplication[p: prop]{
	no p.imply
}

pred getAllImplied[p,p': prop]{
	p' in p.^imply
}

pred getAllRevImplied[p,p': prop]{
	p' in p.^~imply
}

/*pred getAllRevImplied[p: prop]{
	closureOnImplication.imply = p.^(~imply)
}*/



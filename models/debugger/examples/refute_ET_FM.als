--The set of booleans is partitioned into
abstract sig Boolean {}
--singleton sets True and False.
one sig True, False extends Boolean {}  
--Each literal has an associated negation.
sig Literal { neg: Literal } 
-- Negation is symmetric and irreﬂexive.
fact { 
		neg = ~neg && (no iden & neg) 
} 
--Each clause contains a set of literals.
sig Clause { lits: set Literal } 
--One empty clause is denoted Conﬂict.
one sig Conﬂict extends Clause {} { no lits } 
--Every clause other than Conﬂict is nonempty.
fact { 
		all c: Clause - Conﬂict | some c.lits 
} 
--No clause has both a literal and its negation.
fact { 
		--all c: Clause | no c.lits & c.lits.neg 
} 
--Resolving clauses c1 and c2 yields r if
pred resolve [c1, c2, r: Clause] { 
	-- c1 contains some literal x, c2 contains !x,
	some x: c1.lits & c2.lits.neg | 
		--and r is a union of c1 and c2 minus x and !x.
		r.lits = (c1.lits + c2.lits) - (x + x.neg) 
}
-- Each refutation consists of
sig Refutation { 
	--a set of nonempty clauses called ‘sources,’
	sources: some Clause - Conﬂict, 
	--a set of clauses called ‘resolvents,’ and
	resolvents: set Clause, 
	--a set of edges from clauses to resolvents,
	edges: (sources + resolvents)->resolvents 
}{ -- such that
	-- 1) The edge relation is acyclic;
	no ^edges & iden 
	-- 2) Every resolvent has some incoming edges;
	all r: resolvents | some edges.r 
	-- 3) The empty clause is a resolvent;
	Conﬂict in resolvents 
	-- 4) For every source or resolvent n1 and n2
	all n1, n2: sources + resolvents | 
		-- for every resolvent r
		all r: resolvents | 
			-- there are two edges hn1, ri and hn2, ri
			((n1 + n2)->r in edges 
				-- if and only if n1 and n2 resolve to r.
				<=> resolve[n1, n2, r]) 
}
sig Instance {
	--Each instance has a nonempty set of clauses,
	clauses: some Clause, 
	-- and each literal is assigned at most one value.
	assign: Literal->lone Boolean 
}{
	-- Each mentioned literal is assigned a value,
	all lit: clauses.lits | 
		-- and its negation has the opposite value.
		assign[lit] = Boolean - assign[lit.neg] 
	-- Each clause has at least one true literal.
	all c: clauses | True in assign[c.lits] 
}
pred p[]{
not( all i: Instance | no ref: Refutation | ref.sources = i.clauses)
}

run{ p}
check { all i: Instance | no ref: Refutation | ref.sources = i.clauses } for 3

module tour/addressBook3d ----- this is the final model in fig 2.18

--open util/ordering [Book] as BookOrder
//open temporal_logics/ctl[Book]
abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends Name { }

abstract sig Bool {}

one sig True, False extends Bool{}

uniq 
sig Book {
	p: Bool,
	names: set  Name,
	addr: names->some Target//,
//    sigma: set Book
} {
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
	p = True iff (all n: names | some /*lookup [b,n]*/  (n.^(addr) & Addr))
//	all b,b':Book|((b.addr=b'.addr) implies b=b')
}

/*
----------------------------------
--uniq
 one 
sig TS{
	S0:   Book,
	sigma: Book -> Book
}{
	all b,b':Book| 
		((b' in nextState[b]) implies
		(some n: Name, t: Target | add [b, b', n, t] or del [b, b', n, t]))
}

pred add [b, b': Book, n: Name, t: Target] {
	t in Addr or some lookup [b, Name&t]
	b'.addr = b.addr + n->t
	b != b'
}

pred del [b, b': Book, n: Name, t: Target] {
	b != b'
	no b.addr.n or some n.(b.addr) - t
	b'.addr = b.addr - n->t
}

fun lookup [b: Book, n: Name] : set Addr { n.^(b.addr) & Addr }

pred init [b: Book]  { no b.addr }

------------------------------------------------------

assert delUndoesAdd {
	all b, b', b'': Book, n: Name, t: Target |
		no n.(b.addr) and add [b, b', n, t] and del [b', b'', n, t]
		implies
		b.addr = b''.addr
}

// This should not find any counterexample.
--check delUndoesAdd for 3

------------------------------------------------------

assert addIdempotent {
	all b, b', b'': Book, n: Name, t: Target |
		add [b, b', n, t] and add [b', b'', n, t]
		implies
		b'.addr = b''.addr
}

// This should not find any counterexample.
--check addIdempotent for 3

------------------------------------------------------

assert addLocal {
	all b, b': Book, n, n': Name, t: Target |
		add [b, b', n, t] and n != n'
		implies
		lookup [b, n'] = lookup [b', n']
}

// This should not find any counterexample.
--check addLocal for 3 but 2 Book

------------------------------------------------------

assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
}


fact{
	init[initialState]
	all b,b':Book|((b.addr=b'.addr and b.names=b'.names and b.p = b'.p) implies b=b')
}

fun initialState: Book { TS.S0 }

fun nextState: Book -> Book{ TS.sigma }

// Every state has some next state:
//fact {Book = TS.sigma.Book}

pred MC[]{
not	 CTL_MC[AG[p.True]]
}

pred CTL_MC[phi:Book]{
	TS.S0 in phi
}

fun AG[phi:Book]:Book { not_ctl[EF[not_ctl[phi]]] }

fun not_ctl[phi:Book]:Book { Book - phi }

fun EF[phi:Book]:Book { (*(TS.sigma)).phi }

// This should not find any counterexample.
--check lookupYields for 3 but 4 Book
// Scope 14: 1 min 14 sec
--check MC for 10 but 4 Book

// Scope 15: 2 min 57 sec
--check MC for 11 but 4 Book

// Scope 16: 9 min 15 sec
--check MC for 12 but 4 Book

//Scope 17: > 1 h
--check MC for 13 but 4 Book

//run {}  for 0 but exactly 1 Addr, exactly 2 Alias,exactly 1 Group, exactly 86 Book

// This should not find any counterexample.
--check lookupYields for 6
--check MC for 6
*/
inst i{0,exactly 2 Addr, exactly 2 Alias,exactly 1 Group}

pred p[]{}

run 
//CTL_MC 
p
//MC
for i

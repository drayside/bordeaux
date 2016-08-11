module examples/toys/birthday

/*
 * Birthday Book
 *
 * A classic Z example to explain the basic form of an Alloy model. For the original,
 * see J.M. Spivey, The Z Notation, Second Edition, Prentice Hall, 1992.
 *
 * A birthday book has two fields: known, a set of names (of persons whose birthdays are known),
 * and date, a function from known names to dates. The operation AddBirthday adds an association
 * between a name and a date; it uses the relational override operator (++), so any existing
 * mapping from the name to a date is replaced. DelBirthday removes the entry for a given name.
 * FindBirthday obtains the date d for a name n. The argument d is declared to be optional (that is,
 * a singleton or empty set), so if there is no entry for n, d will be empty. Remind gives the set
 * of names whose birthdays fall on a particular day.
 *
 * The assertion AddWorks says that if you add an entry, then look it up, you get back what you
 * just entered. DelIsUndo says that doing DelBirthday after AddBirthday undoes it, as if the add
 * had never happened. The first of these assertions is valid; the second isn't.
 *
 * The function BusyDay shows a case in which Remind produces more than one card.
 *
 * author: Daniel Jackson, 11/14/01
 */

sig Name {}
sig Date {}
sig BirthdayBook {known: set Name, date: known -> one Date}//, date2: lone Name -> one Date}

pred AddBirthday [bb, bb': BirthdayBook, n: Name, d: Date] {
    bb'.date = bb.date ++ (n->d)
    }

pred DelBirthday [bb, bb': BirthdayBook, n: Name] {
    bb'.date = bb.date - (n->Date)
    }

pred FindBirthday [bb: BirthdayBook, n: Name, d: lone Date] {
    d = bb.date[n]
    }

pred Remind [bb: BirthdayBook, today: Date, cards: set Name] {
    cards = (bb.date).today
    }

pred InitBirthdayBook [bb: BirthdayBook] {
    no bb.known
    }

assert AddWorks {
    all bb, bb': BirthdayBook, n: Name, d: Date, d': lone Date |
        AddBirthday [bb,bb',n,d] && FindBirthday [bb',n,d'] => d = d'
    }

assert DelIsUndo {
    all bb1,bb2,bb3: BirthdayBook, n: Name, d: Date|
        AddBirthday [bb1,bb2,n,d] && DelBirthday [bb2,bb3,n]
            => bb1.date = bb3.date
    }

check AddWorks for 3 but 2 BirthdayBook expect 0
check DelIsUndo2 for 3 but 3 BirthdayBook expect 0

pred BusyDay [bb: BirthdayBook, d: Date]{
    some cards: set Name | Remind [bb,d,cards] && !lone cards
    }

run BusyDay for 3 but 1 BirthdayBook expect 1

/** Fikayo Modified **/

/**
* DellsUndo fails because it attempts to assert that bb1.date = bb3.date after deletion.
* This is incorrect because the birthday n->d added to bb2 could have previously existed in bb1 as n->d'
* This relation n-> d' would be replaced by n->d when added to bb2.
* However, the deletion of n would completely remove all relations from n from bb3
* As a result bb1 would still have the original relation of bb1->n->d' while bb3 would not have any relations involving n.
* Consequently, the assertion that bb1.date = bb3.date would be false with the satement above serving as a counterexample.
*
* DellsUndo2 fixes the issue and instead makes one of the following checks:
*	n->d exists in bb2.date but n does not exist in bb3.known
*	adding (or replacing) n->d to bb1.date, then removing n-> from bb1.date yields bb1.date = bb3.date
*	removing n from bb1.known is equal to bb3.known
*/
assert DelIsUndo2 {
    all bb1,bb2, bb3: BirthdayBook, n: Name, d: Date|
        AddBirthday [bb1,bb2,n,d] && DelBirthday [bb2, bb3, n] 
		// Any of the following constraints will satisfy the neccessary check
		=> n->d in bb2.date and n not in bb3.known
		// => ((bb1.date ++ n->d) - n->d) = bb3.date
		// => (bb1.known - n) = bb3.known
    }

/*Instance Checks*/
pred includeInstance[	bb: set BirthdayBook, 
					n: set Name, 
					d: set Date, 
					known: BirthdayBook -> Name, 
					date: BirthdayBook -> Name -> Date] {

	// known checks
	BirthdayBook.known in n
	known.Name in bb

	// date checks
	Name.(BirthdayBook.date) in d
	(BirthdayBook.date).Date in n
	(date.Date).Name in bb
}

pred structuralConstraint[	bb: set BirthdayBook, 
						n: set Name, 
						d: set Date, 
						known: BirthdayBook -> Name, 
						date: BirthdayBook -> Name -> Date] {//,
						// date2: BirthdayBook -> Name -> Date] {
	// all bb': bb |/* also need to  if bb.known is a set of Names */ #(bb'.known) >= 1 implies  one (bb'.known).(bb'.date)
	// all bb': bb |/* also need to check if bb.known is a set of Names */ (some n : Name | n in bb'.known) => one (bb'.known).(bb'.date)

	// all bb' : bb | bb'.date in Name set -> one Date
	// date in ((bb -> set Name) -> one Date)
	// date in bb -> (Name set -> one Date)
	
	known in (bb -> set n)
	// all bb': bb | bb'.known in bb'.(bb -> set Name)

	// all bb': bb | bb'.date in (bb'.known -> one d)
	date in (known -> one d)
	// date2 in (bb -> lone n -> one d)

}

pred isInstance[	bb: set BirthdayBook, 
				n: set Name, 
				d: set Date, 
				known: BirthdayBook -> Name, 
				date: BirthdayBook -> Name -> Date] {
				// date2: BirthdayBook -> Name -> Date] {

	includeInstance[bb, n, d, known, date]
	structuralConstraint[bb, n, d, known, date]//, date2]
}

pred deltaBirthdayBook[bb: set BirthdayBook, bb': set BirthdayBook, bb'': set BirthdayBook] {
	bb != bb' implies (bb'' = bb' - bb and bb'' + bb = bb') else no bb''
}

pred deltaNames[n: set Name, n': set Name, n'': set Name] {
	n != n' implies (n'' = n' - n and n'' + n = n') else no n''
}

pred deltaDates[d: set Date, d': set Date, d'': set Date] {
	d != d' implies (d'' = d' - d and d'' + d = d') else no d''
}

pred deltaKnown[k: BirthdayBook -> Name, k': BirthdayBook -> Name, k'': BirthdayBook -> Name] {
	k != k' implies (k'' = k' - k and k'' + k = k') else no k''
}

pred deltaDate[d: BirthdayBook -> Name -> Date, d': BirthdayBook -> Name -> Date, d'': BirthdayBook -> Name -> Date] {
	d != d' implies (d'' = d' - d and d'' + d = d') else no d''
}

pred findMarginalInstances[] {
	some bb, bb', bb'': set BirthdayBook, n, n', n'': set Name, d, d', d'': set Date,
		k, k', k'': BirthdayBook -> Name, dt, dt', dt'': BirthdayBook -> Name -> Date | {
			(isInstance[bb, n, d, k, dt]
			and not isInstance[bb', n', d', k', dt']
			and deltaBirthdayBook[bb, bb', bb''] 
			and deltaNames[n, n', n''] 
			and deltaDates[d, d', d''] 
			and deltaKnown[k, k', k''] 
			and deltaDate[dt, dt', dt''])
		and
			all bb1, bb1', bb1'': set BirthdayBook, n1, n1', n1'': set Name, d1, d1', d1'': set Date,
			k1, k1', k1'': BirthdayBook -> Name, dt1, dt1', dt1'': BirthdayBook -> Name -> Date | {
				(isInstance[bb1, n1, d1, k1, dt1]
				and not isInstance[bb1', n1', d1', k1', dt1']
				and deltaBirthdayBook[bb1, bb1', bb1''] 
				and deltaNames[n1, n1', n1''] 
				and deltaDates[d1, d1', d1''] 
				and deltaKnown[k1, k1', k1''] 
				and deltaDate[dt1, dt1', dt1''])
			implies
				(
				#bb1'' >= #bb''
				and #n1'' >= #n''
				and #d1'' >= #d''
				and (no dt'' or #k1'' >= #k'')
				and (no k'' or #dt1'' >= #dt'') 
				)
			}
	}
}

assert instanceChecks {
	isInstance[BirthdayBook, Name, Date, known, date]//, date2]
}

/*run {
	findMarginalInstances
	no known
	no date
} for 0 but exactly 3 BirthdayBook, 10 Name, 10 Date, 0..400 Int
*/
check instanceChecks for 5
// run {isInstance[BirthdayBook, Name, Date, known, date]}

/*fact {
	isInstance[BirthdayBook, Name, Date, known, date]
}

run{}
*/

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


sig Name {}
sig Date {}
sig BirthdayBook {known: set Name, date: known -> one Date}


pred diffName[name: set Name, name': set Name, name'': set Name] {
    name != name' implies (name'' = name' - name and name'' + name = name') else no name''
}

pred diffDate[date: set Date, date': set Date, date'': set Date] {
    date != date' implies (date'' = date' - date and date'' + date = date') else no date''
}

pred diffBirthdayBook[birthdayBook: set BirthdayBook, birthdayBook': set BirthdayBook, birthdayBook'': set BirthdayBook] {
    birthdayBook != birthdayBook' implies (birthdayBook'' = birthdayBook' - birthdayBook and birthdayBook'' + birthdayBook = birthdayBook') else no birthdayBook''
}

pred diffbirthdayBook_known[birthdayBook_known: BirthdayBook->Name, birthdayBook_known': BirthdayBook->Name, birthdayBook_known'': BirthdayBook->Name] {
    birthdayBook_known != birthdayBook_known' implies (birthdayBook_known'' = birthdayBook_known' - birthdayBook_known and birthdayBook_known'' + birthdayBook_known = birthdayBook_known') else no birthdayBook_known''
}

pred diffbirthdayBook_date[birthdayBook_date: BirthdayBook->Name->Date, birthdayBook_date': BirthdayBook->Name->Date, birthdayBook_date'': BirthdayBook->Name->Date] {
    birthdayBook_date != birthdayBook_date' implies (birthdayBook_date'' = birthdayBook_date' - birthdayBook_date and birthdayBook_date'' + birthdayBook_date = birthdayBook_date') else no birthdayBook_date''
}

pred structuralConstraints [name: set Name, date: set Date, birthdayBook: set BirthdayBook, birthdayBook_known: BirthdayBook->Name, birthdayBook_date: BirthdayBook->Name->Date] {
    (all p_this: one birthdayBook | ((p_this . birthdayBook_known) in name))
    ((birthdayBook_known . univ) in birthdayBook)
    (all p_this: one birthdayBook | ((((p_this . birthdayBook_date) in ((p_this . birthdayBook_known) -> birthdayBook_date)) && (all v0: one (p_this . birthdayBook_known) | (one (v0 . (p_this . birthdayBook_date)) && ((v0 . (p_this . birthdayBook_date)) in birthdayBook_date)))) && (all v1: one birthdayBook_date | (((p_this . birthdayBook_date) . v1) in (p_this . birthdayBook_known)))))
    (((birthdayBook_date . univ) . univ) in birthdayBook)
}

pred includeInstance [name: set Name, date: set Date, birthdayBook: set BirthdayBook, birthdayBook_known: BirthdayBook->Name, birthdayBook_date: BirthdayBook->Name->Date] {
    (birthdayBook_known.Name) in BirthdayBook
    (BirthdayBook.birthdayBook_known) in Name
    ((birthdayBook_date.Date).Name) in BirthdayBook
    ((BirthdayBook.birthdayBook_date).Date) in Name
    (Name.(BirthdayBook.birthdayBook_date)) in Date
}

pred isInstance [name: set Name, date: set Date, birthdayBook: set BirthdayBook, birthdayBook_known: BirthdayBook->Name, birthdayBook_date: BirthdayBook->Name->Date] {
    includeInstance[Name, Date, BirthdayBook, birthdayBook_known, birthdayBook_date]
    structuralConstraints[Name, Date, BirthdayBook, birthdayBook_known, birthdayBook_date]
}

pred findMarginalInstances[] {
    some name, name', name'': set Name, date, date', date'': set Date, birthdayBook, birthdayBook', birthdayBook'': set BirthdayBookbirthdayBook_known, birthdayBook_known', birthdayBook_known'': set BirthdayBook->Name, birthdayBook_date, birthdayBook_date', birthdayBook_date'': set BirthdayBook->Name->Date | {
            (
            isInstance[name, date, birthdayBookbirthdayBook_known, birthdayBook_date]
            and not isInstance[name', date', birthdayBook'birthdayBook_known', birthdayBook_date']
            and deltaName[name, name', name'']
            and deltaDate[date, date', date'']
            and deltaBirthdayBook[birthdayBook, birthdayBook', birthdayBook'']
            and deltaBirthdayBook_known[birthdayBook_known, birthdayBook_known', birthdayBook_known'']
            and deltaBirthdayBook_date[birthdayBook_date, birthdayBook_date', birthdayBook_date'']
            )
        and
            all name1, name1', name1'': set Name, date1, date1', date1'': set Date, birthdayBook1, birthdayBook1', birthdayBook1'': set BirthdayBookbirthdayBook_known1, birthdayBook_known1', birthdayBook_known1'': set BirthdayBook->Name, birthdayBook_date1, birthdayBook_date1', birthdayBook_date1'': set BirthdayBook->Name->Date | {
                    (
                    isInstance[name1, date1, birthdayBook1birthdayBook_known1, birthdayBook_date1]
                    and not isInstance[name1', date1', birthdayBook1'birthdayBook_known1', birthdayBook_date1']
                    and deltaName[name1, name1', name1'']
                    and deltaDate[date1, date1', date1'']
                    and deltaBirthdayBook[birthdayBook1, birthdayBook1', birthdayBook1'']
                    and deltaBirthdayBook_known[birthdayBook_known1, birthdayBook_known1', birthdayBook_known1'']
                    and deltaBirthdayBook_date[birthdayBook_date1, birthdayBook_date1', birthdayBook_date1'']
                    )
                implies
                    (
                    )
            }
    }
}

// Borrowed from Sample Models/examples/systems/file_system.als
abstract sig Object {}
sig Name {}

sig File extends Object {} /*{some d: Dir | this in d.entries.contents  }*/

pred structural[]{
	all d: Dir| lone d.parent

	all de: DirEntry| one de.name
	all de: DirEntry| one de.contents

}

pred appendedFacts{
	--some d: Dir | this in d.entries.contents
	all f: File | some d: Dir | f in d.entries.contents

	--parent = this.~@contents.~@entries
	all d: Dir|  d.parent = d.~@contents.~@entries
	--all e1, e2 : entries | e1.name = e2.name => e1 = e2
	all d: Dir| all e1, e2 : d.entries | e1.name = e2.name => e1 = e2
	-- this !in this.^@parent
	all d: Dir| d !in d.^@parent
	--this != Root => Root in this.^@parent
	all d: Dir| d != Root => Root in d.^@parent
	-- no parent
	all r: Root|  no r.parent
	-- one this.~entries
	all de: DirEntry| one de.~entries
}

sig Dir extends Object {
  entries: set DirEntry,
  parent: set Dir
} /*{
  parent = this.~@contents.~@entries
  all e1, e2 : entries | e1.name = e2.name => e1 = e2
  this !in this.^@parent
  this != Root => Root in this.^@parent
}*/

one sig Root extends Dir {} /*{ no parent }*/

lone sig Cur extends Dir {}

sig DirEntry {
  name: set Name,
  contents: set Object
} /*{
  one this.~entries
}*/

pred OneParent_correctVersion {
    all d: Dir - Root | (one d.parent && one contents.d)
}

run OneParent_correctVersion for 3

pred newOneParent_correctVersion{
	OneParent_correctVersion
	appendedFacts
}

pred Not_newOneParent_correctVersion{
	not newOneParent_correctVersion
}

pred Not_Structural{
	not structural
}

pred normal{
	newOneParent_correctVersion
	structural
}

pred withStructural{
	Not_Structural
	Not_newOneParent_correctVersion
}

run normal

run withStructural

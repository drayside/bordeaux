// Borrowed from Sample Models/examples/systems/file_system.als
abstract sig Object {}

sig Name {}

sig File extends Object {} { some d: Dir | this in d.entries.contents }

sig Dir extends Object {
  entries: set DirEntry,
  parent: lone Dir
} /*{
  parent = this.~@contents.~@entries
  all e1, e2 : entries | e1.name = e2.name => e1 = e2
  this !in this.^@parent
  this != Root => Root in this.^@parent
}
*/
one sig Root extends Dir {} { no parent }

lone sig Cur extends Dir {}

sig DirEntry {
  name: Name,
  contents: Object
} {
  one this.~entries
}

pred OneParent_correctVersion {
    all d: Dir - Root | (one d.parent && one contents.d)
}

run OneParent_correctVersion for 3

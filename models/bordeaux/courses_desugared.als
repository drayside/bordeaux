abstract sig Course{reqs: set Course}
// one sig ECE155, ECE240, ECE250, ECE351 extends Course{}
sig ECE155 extends Course{}
sig ECE240 extends Course{}
sig ECE250 extends Course{}
--one sig ECE351 extends Course{}

sig Program{courses: set Course}

//fact preRequisites{
pred preRequisites{
  no ECE155.reqs
  ECE155 = ECE240.reqs
  ECE155 = ECE250.reqs
--  ECE250 = ECE351.reqs
}



fun successfulProgram[]: Program{
  {p: Program| eq[#p.courses, 2] and
               all c: p.courses| some c.reqs implies c.reqs in p.courses}
}

pred showSuccesfullPrograms[]{
	preRequisites
  some successfulProgram
}

run showSuccesfullPrograms --for 3 Int

pred structural{
	one ECE155
	one ECE240
	one ECE250
	one Program
}

pred Not_showSuccesfullPrograms{
	not showSuccesfullPrograms
}

pred Not_structural{
	not structural
}

pred normal{
	showSuccesfullPrograms
	structural
}

pred WithStructural{
	Not_structural
	Not_showSuccesfullPrograms
}


run normal

run WithStructural




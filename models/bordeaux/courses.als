abstract sig Course{reqs: set Course}
one sig ECE155, ECE240, ECE250, ECE351 extends Course{}

fact preRequisites{
  no ECE155.reqs
  ECE155 = ECE240.reqs
  ECE155 = ECE250.reqs
  ECE250 = ECE351.reqs
}

one sig Program{courses: set Course}

fun successfulProgram[]: Program{
  {p: Program| eq[#p.courses, 3] and
               all c: p.courses| some c.reqs implies c.reqs in p.courses}
}

pred showSuccesfullPrograms[]{
  some successfulProgram
}

run showSuccesfullPrograms 


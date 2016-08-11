/**
	This model is completed sliped into the constriants to find out the properites of each constraint.
*/

open util/ordering [State] as so
open util/ordering [Mutex] as mo

sig Process {}
sig Mutex {}

sig State { holds, waits: Process -> Mutex }


pred Initial [s: State]  { no s.holds + s.waits }

pred IsFree [s: State, m: Mutex] {
   // no process holds this mutex
   no m.~(s.holds)
   // all p: Process | m !in p.(this.holds)
}

pred IsStalled [s: State, p: Process] { some p.(s.waits) }

pred GrabMutex [s: State, p: Process, m: Mutex, s': State] {
   // a process can only act if it is not
   // waiting for a mutex
   !s.IsStalled[p]
   // can only grab a mutex we do not yet hold
   m !in p.(s.holds)
   s.IsFree[m] => {
      // if the mutex is free, we now hold it,
      // and do not become stalled
      p.(s'.holds) = p.(s.holds) + m
      no p.(s'.waits)
   } else {
    // if the mutex was not free,
    // we still hold the same mutexes we held,
    // and are now waiting on the mutex
    // that we tried to grab.
    p.(s'.holds) = p.(s.holds)
    p.(s'.waits) = m
  }
  all otherProc: Process - p | {
     otherProc.(s'.holds) = otherProc.(s.holds)
     otherProc.(s'.waits) = otherProc.(s.waits)
  }
}

pred ReleaseMutex [s: State, p: Process, m: Mutex, s': State] {
   !s.IsStalled[p]
   m in p.(s.holds)
   p.(s'.holds) = p.(s.holds) - m
   no p.(s'.waits)
   no m.~(s.waits) => {
      no m.~(s'.holds)
      no m.~(s'.waits)
   } else {
      some lucky: m.~(s.waits) | {
        m.~(s'.waits) = m.~(s.waits) - lucky
        m.~(s'.holds) = lucky
      }
   }
  all mu: Mutex - m {
    mu.~(s'.waits) = mu.~(s.waits)
    mu.~(s'.holds)= mu.~(s.holds)
  }
}

// for every adjacent (pre,post) pair of States,
// one action happens: either some process grabs a mutex,
// or some process releases a mutex,
// or nothing happens (have to allow this to show deadlocks)
pred GrabOrRelease  {
    Initial[so/first] &&
    (
    all pre: State - so/last  | let post = so/next [pre] |
       (post.holds = pre.holds && post.waits = pre.waits)
        ||
       (some p: Process, m: Mutex | pre.GrabMutex [p, m, post])
        ||
       (some p: Process, m: Mutex | pre.ReleaseMutex [p, m, post])

    )
}

pred Deadlock  {
         some Process
         some s: State | all p: Process | some p.(s.waits)
}

pred GrabbedInOrder  {
   all pre: State - so/last |
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.holds) |
        let grabbed = have - had |
           some grabbed => grabbed in mo/nexts[had]
}

pred GrabbedInOrder_fix1  {
   all pre: State - so/last |
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.holds) |
        let grabbed = have - had |
           (some had and some grabbed) => grabbed in mo/nexts[had]
}


fun UpdatedNextsMO[m: Mutex]: Mutex{
	no m 	implies Mutex
			else  mo/nexts[m]
}

pred GrabbedInOrder_fix2  {
   all pre: State - so/last |
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.holds) |
        let grabbed = have - had |
          (some grabbed) => (grabbed in UpdatedNextsMO[had])
}

pred GrabbedInOrder_fix3  {
   all pre: State - so/last |
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.holds) |
        let grabbed = have - had |
          (/*some had and */some grabbed) => (no grabbed & mo/prevs[had])
}

pred GrabbedInOrder_fix4  {
   all p: Process |
	all pre: State - so/last |
     let post = so/next[pre] |
        let had = p.(pre.holds), have = p.(post.holds) |
        let grabbed = have - had |
          (/*some had and */some grabbed) => (no grabbed & mo/prevs[had])
}

pred GrabbedInOrder_fix5  {
   all p: Process |
	all pre: State - so/last |
     let post = so/next[pre] |
        let had = p.(pre.holds), have = p.(post. (waits + holds) ) |
        let grabbed = have - had |
          (/*some had and */some grabbed) => (no grabbed & mo/prevs[had])
}

assert /*DijkstraPreventsDeadlocks*/assert1 {
   some Process && GrabOrRelease && GrabbedInOrder => ! Deadlock
}

pred ShowDijkstra  {
    GrabOrRelease && Deadlock
    some waits
}
pred U{! Deadlock }

pred A {some Process}
pred B {GrabOrRelease}
pred C {GrabbedInOrder}
pred CF1 {GrabbedInOrder_fix1}
pred CF2 {GrabbedInOrder_fix2}
pred CF3 {GrabbedInOrder_fix3}
pred CF4 {GrabbedInOrder_fix4}
pred CF5 {GrabbedInOrder_fix5}

pred AB {A and B}

pred BC {B and C}

pred AC {A and C}

pred CF4NOTU{ not ((B and A and CF4 ) implies U)}

pred CF4U{ ((B and A and CF4 ) implies U)}
pred CF4ANT{ ((B and A and CF4 ))}

pred EXCF4N{
	
	some disj s0,s1,s2,s3,s4: State, disj p0,p1:Process, m0,m1,m2,m3: Mutex|{
		Process = p0 + p1

		s0 = so/first
		s1 = so/next[s0]
		s2 = so/next[s1]
		s3 = so/next[s2]
		s4 = so/next[s3]

		m0 = mo/first
		m1 = mo/next[m0]
		m2 = mo/next[m1]
		m3 = mo/next[m2]


		holds = s1->p1->m0 + 
				s2->p1->m0 + s2->p0->m1 +
				s3->p1->m0 + s3->p0->m1 +
				s4->p1->m0 + s4->p0->m1 
		

		waits = s3->p1->m1 +  
				s4->p1->m1 + s4->p0->m0
	}
}


pred EXCF4Y{
	
	some disj s0,s1,s2,s3,s4: State, disj p0,p1:Process, m0,m1,m2,m3: Mutex|{
		Process = p0 + p1

		s0 = so/first
		s1 = so/next[s0]
		s2 = so/next[s1]
		s3 = so/next[s2]
		s4 = so/next[s3]

		m0 = mo/first
		m1 = mo/next[m0]
		m2 = mo/next[m1]
		m3 = mo/next[m2]


		holds = s1->p1->m0 + 
				s2->p1->m0 + s2->p0->m1 +
				s3->p1->m0 + s3->p0->m1 +
				s4->p1->m0 + s4->p0->m1 
		

		waits = s3->p1->m1 +  
				s4->p1->m1 //+ s4->p0->m0
	}
}

/*run U for 5 State, 5 Process, 4 Mutex
run A for 5 State, 5 Process, 4 Mutex
run B for 5 State, 5 Process, 4 Mutex
run C for 5 State, 5 Process, 4 Mutex

run CF1 for 5 State, 5 Process, 4 Mutex
run CF2 for 5 State, 5 Process, 4 Mutex
run CF3 for 5 State, 5 Process, 4 Mutex
run CF4 for 5 State, 5 Process, 4 Mutex
run CF5 for 5 State, 5 Process, 4 Mutex*/

/*run U for 5 State, 5 Process, 4 Mutex
run A for 5 State, 5 Process, 4 Mutex
run B for 5 State, 5 Process, 4 Mutex
run C for 5 State, 5 Process, 4 Mutex

run CF1 for 5 State, 5 Process, 4 Mutex
run CF2 for 5 State, 5 Process, 4 Mutex
run CF3 for 5 State, 5 Process, 4 Mutex*/
//run CF4 for 5 State, 5 Process, 4 Mutex
//run CF5 for 5 State, 5 Process, 4 Mutex

--run CF4NOTU for 5 State, 5 Process, 4 Mutex

run CF4U for 5 State, 5 Process, 4 Mutex
run CF4ANT for 5 State, 5 Process, 4 Mutex
run EXCF4N for 5 State, 5 Process, 4 Mutex
run EXCF4Y for 5 State, 5 Process, 4 Mutex

/*fact{
	some State
	some Process
	some Mutex
}*/


//run {some Process && GrabOrRelease && GrabbedInOrder}  for 5 State, 5 Process, 4 Mutex
//check assert1 for 5 State, 5 Process, 4 Mutex




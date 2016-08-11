//open general_properties

/*
 * Models how mutexes are grabbed and released by processes, and
 * how Dijkstra's mutex ordering criterion can prevent deadlocks.
 *
 * For a detailed description, see:
 *   E. W. Dijkstra, Cooperating sequential processes. Technological
 *   University, Eindhoven, The Netherlands, September 1965.
 *   Reprinted in Programming Languages, F. Genuys, Ed., Academic
 *   Press, New York, 1968, 43-112.
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

pred GrabMutexActualFix [s: State, p: Process, m: Mutex, s': State] {
   // a process can only act if it is not
   // waiting for a mutex
   !s.IsStalled[p]
   // can only grab a mutex we do not yet hold
   m !in p.(s.holds)
   // mutexes are grabbed in order
   all m': p.(s.holds) | mo/lt[m',m]
--For the second implication
--	m in mo/next[p.(s.holds) ]
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

pred NoChange[s,s': State]{
	(s.(holds) = s'.(holds) and  s.(waits) = s'.(waits))
}

pred GrabOrReleaseActualFix  {
    Initial[so/first] &&
    (
    all pre: State - so/last  | let post = so/next [pre] |
       (post.holds = pre.holds && post.waits = pre.waits)
        ||
       (some p: Process, m: Mutex | pre.GrabMutexActualFix [p, m, post])
        ||
       (some p: Process, m: Mutex | pre.ReleaseMutex [p, m, post])

    )
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
    GrabOrRelease_2//_expanded
}


pred GrabOrRelease_2  {
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

//It should be equal to GrabOrRelease_2  but  the prediactes are inlined.
pred GrabOrRelease_2_expanded  {
    all pre: State - so/last  | let post = so/next [pre] |
       (post.holds = pre.holds && post.waits = pre.waits)
        ||
(
some p: Process, m: Mutex |{
   // a process can only act if it is not
   // waiting for a mutex
   !some p.(pre.waits)
   // can only grab a mutex we do not yet hold
   m !in p.(pre.holds) 
   no m.~(pre.holds) => {
      // if the mutex is free, we now hold it,
      // and do not become stalled
      p.(post.holds) = p.(pre.holds) + m
      no p.(post.waits)
   } else {
    // if the mutex was not free,
    // we still hold the same mutexes we held,
    // and are now waiting on the mutex
    // that we tried to grab.
    p.(post.holds) = p.(pre.holds)
    p.(post.waits) = m
  }
  all otherProc: Process - p | {
     otherProc.(post.holds) = otherProc.(pre.holds)
     otherProc.(post.waits) = otherProc.(pre.waits)
  }
})
        ||

(some p: Process, m: Mutex |{
   !some p.(pre.waits)
   m in p.(pre.holds)
   p.(post.holds) = p.(pre.holds) - m
   no p.(post.waits)
   no m.~(pre.waits) => {
      no m.~(post.holds)
      no m.~(post.waits)
   } else {
      some lucky: m.~(pre.waits) | {
        m.~(post.waits) = m.~(pre.waits) - lucky
        m.~(post.holds) = lucky
      }
   }
  all mu: Mutex - m {
    mu.~(post.waits) = mu.~(pre.waits)
    mu.~(post.holds)= mu.~(pre.holds)
  }
})
}

pred Deadlock  {
         some Process
         some s: State | all p: Process | some p.(s.waits)
}


pred GrabbedInOrderIncorrect  {
   all pre: State - so/last | 
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.holds) |
        let grabbed = have - had |
           --some grabbed => grabbed in mo/nexts[had]
           some grabbed => no grabbed & mo/prevs[had]
           --(some had and some grabbed) => grabbed in mo/nexts[had]
}

pred newGrabbedInOrder[pre:State]{

//all p:Process |
	let mj= Process.(so/next[pre].(waits))| let mi= Process.(pre.(waits)) | 
--Rule 7	
		(mi in mj)/*Exapnding*/ and ( #(mj-mi) =1)/*Pace rate*/ and (/*some mi implies*/ ( all m:(mj-mi)|all m':mi |  m in mo/nexts[/*mo/next[*/m'/*]*/]) )/*Increase Order Not exactly the next*/
--Rule 13		(mj in mi)/*Exapnding*/ and ( #(mi-mj) =1)/*Pace rate*/ and (/*some mi implies*/ ( all m:(mi-mj)|all m':mj |  m in mo/nexts[/*mo/next[*/m'/*]*/]) )/*Increase Order Not exactly the next*/
//or
//		(mj in mi)/*Shriking*/ and (#(mi-mj)=1)/*Pace rate*/ /*and (all m:(mi-mj)| all m':mj| m in mo/nexts[mo/next[m']])*/
//or 
--rule 8		(mi = mj) 
}

pred newGrabbedInOrderHolds[pre:State]{

all p:Process |
	let mj= p.(so/next[pre].(holds))| let mi= p.(pre.(holds)) | 
--		(mi in mj)/*Exapnding*/ and ( #(mj-mi) =1)/*Pace rate*/ and (/*some mi implies*/ ( all m:(mj-mi)|all m':mi |  m in mo/nexts[mo/next[m']]) )/*Increase Order Not exactly the next*/
		(mi in mj)/*Exapnding*/ and ( #(mj-mi) =1)/*Pace rate*/ and (/*some mi implies*/ ( all m:(mj-mi)|all m':mi |  m in mo/nexts[/*mo/next[*/m'/*]*/]) )/*Increase Order Not exactly the next*/
or
		(mj in mi)/*Shriking*/ and (#(mi-mj)=1)/*Pace rate*/ /*and (all m:(mi-mj)| all m':mj| m in mo/nexts[mo/next[m']])*/
or 
		(mi = mj) 
}


pred GrabbedInOrderHelper[pre:State]  {
//   all pre: State - so/last |
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.(holds+waits)), have = p.(post.(holds+waits)) |
        let grabbed = have - had |
//           some grabbed => grabbed in mo/nexts[had] --the instail case
//			(some had and some grabbed) => grabbed in mo/nexts[had]
			(some had and some grabbed) => (no grabbed & mo/prevs[had])
//			(no had and some grabbed) => grabbed in {m:Mutex| mo/lt[had,m]}

//		(no had and some grabbed) => grabbed=mo/first else
//					 some grabbed => mo/lt[had,grabbed]// grabbed in mo/nexts[had] // mo/lt[had,grabbed] //
}

pred GrabbedInOrderSome/*Corrected*/  { all pre: State - so/last | GrabbedInOrderHelperSomeHad[pre]}


pred GrabbedInOrder/*Corrected*/  {
//  all pre: State - so/last | GrabbedInOrderHelper[pre] --The correct version
//   all pre: State - so/last | GrabbedInOrderHelperLocal[pre]
//   all pre: State - so/last | GrabbedInOrderHelperSomeHad[pre]
//   all pre: State - so/last | GrabbedInOrderHelperOrder[pre]
//	 all pre: State - so/last | GrabbedInOrderHelperOrderAndLocal[pre]
//	 all pre: State - so/last | GrabbedInOrderHelperSomeHadAndLocal[pre]
//	  all pre: State - so/last | GrabbedInOrderHelperMoreWaiting[pre]
//	  all pre: State - so/last | GrabbedInOrderHelperOrderAndWaitsAndLocal[pre]
//	  all pre: State - so/last | GrabbedInOrderHelperOrderAndWaits[pre]
//	  all pre: State - so/last | GrabbedInOrderHelperOrderAndWaitsAndLocal[pre]
//	  all pre: State - so/last | GrabbedInOrderHelperSomeHadAndOrder[pre]
//	  all pre: State - so/last | GrabbedInOrderHelperSomeHadAndOrderAndLocal[pre]
//	  all pre: State - so/last | GrabbedInOrderHelperSomeHadAndOrderAndWaits[pre]
	  all pre: State - so/last | GrabbedInOrderHelperSomeHadAndOrderAndWaitsAndLocal[pre]
	

//	  all pre: State - so/last | newGrabbedInOrderHolds[pre]

/*     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.holds) |
        let grabbed = have - had |
           some grabbed => grabbed in mo/nexts[had]*/
}


--Mutation: Change Global to Local
--No Instance because of the conflict with the initial constraint.
pred GrabbedInOrderHelperLocal[pre:State]  {
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.holds), have = p.(post.(holds)) |
        let grabbed = have - had |
			some grabbed => grabbed in mo/nexts[had]
}

pred GrabbedInOrderHelperSomeHad[pre:State]  {
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.(holds)) |
        let grabbed = have - had |
			(some had and some grabbed) => grabbed in mo/nexts[had]
}


pred GrabbedInOrderHelperSomeHadAndLocal[pre:State]  {
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.holds), have = p.(post.(holds)) |
        let grabbed = have - had |
			(some had and some grabbed) => grabbed in mo/nexts[had]
}

//Another representation of initial. Apparently it is not equisatisfiable with GrabbedInOrderHelperInitial
pred GrabbedInOrderHelperSomeHad2[pre:State]  {
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.(holds)) |
        let grabbed = have - had |
			(not Initial[pre] and some grabbed) => grabbed in mo/nexts[had]
}

assert InitialExclusionVariations{
	all pre: State - so/last | GrabbedInOrderHelperSomeHad[pre] <=> GrabbedInOrderHelperSomeHad2[pre]
}

pred GrabbedInOrderHelperOrder[pre:State]  {
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.(holds)) |
        let grabbed = have - had |
			(some grabbed) => (no grabbed & mo/prevs[had])
}

pred GrabbedInOrderHelperOrderAndWaits[pre:State]  {
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.(holds+waits)) |
        let grabbed = have - had |
			(some grabbed) => (no grabbed & mo/prevs[had])
}


--This does not make any instance. The Initial predicate is the root of inconsistency.
pred GrabbedInOrderHelperMoreWaiting[pre:State]  {
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.(holds+waits)) |
        let grabbed = have - had |
			(some grabbed) => grabbed in mo/nexts[had]
}

--We do not need the SomeHad predicate anymore!
pred GrabbedInOrderHelperOrderAndWaitsAndLocal[pre:State]  {
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.holds), have = p.(post.(holds+waits)) |
        let grabbed = have - had |
			(some grabbed) => (no grabbed & mo/prevs[had])
}

pred GrabbedInOrderHelperSomeHadAndOrder[pre:State]  {
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.(holds)) |
        let grabbed = have - had |
			(some had and some grabbed) => (no grabbed & mo/prevs[had])
}


pred GrabbedInOrderHelperSomeHadAndOrderAndLocal[pre:State]  {
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.holds), have = p.(post.(holds)) |
        let grabbed = have - had |
			(some had and some grabbed) => (no grabbed & mo/prevs[had])
}

pred GrabbedInOrderHelperOrderAndLocal[pre:State]  {
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.holds), have = p.(post.(holds)) |
        let grabbed = have - had |
			(some grabbed) => (no grabbed & mo/prevs[had])
}

pred GrabbedInOrderHelperSomeHadAndOrderAndWaits[pre:State]  {
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.(holds+waits)) |
        let grabbed = have - had |
			(some had and some grabbed) => (no grabbed & mo/prevs[had])
}

pred GrabbedInOrderHelperSomeHadAndOrderAndWaitsAndLocal[pre:State]  {
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.holds), have = p.(post.(holds+waits)) |
        let grabbed = have - had |
			(some had and some grabbed) => (no grabbed & mo/prevs[had])
/*and
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.waits), have = p.(post.(waits)) |
        let grabbed = have - had |
			(some had and some grabbed) => (no grabbed & mo/prevs[had])*/
}

--Can Order cover the Initial instancces? The aswer is false. Neither way is true.
assert OrderImpliesInitial{
	all pre: State - so/last |GrabbedInOrderHelperSomeHad[pre] => GrabbedInOrderHelperOrder[pre] 
}

--What SomeHad covers but Order does not
pred SomeHadOrder{
	(some Process) 
 	GrabOrRelease
--	!Deadlock
	not (all pre: State - so/last | GrabbedInOrderHelperSomeHad[pre] )
--	not 
	not (all pre: State - so/last |   GrabbedInOrderHelperOrder[pre] )
}

pred precedence{
	//(some Process) and Initial[so/first] and GrabOrRelease_2 and  GrabbedInOrder
	(some Process) and GrabOrRelease and  GrabbedInOrder //&& (some State.waits)
	

}

assert DijkstraPreventsDeadlocks {
   precedence => ! Deadlock
//precedence =>(	some waits => #holds >= 0)
}

assert FixesAreEquiSAT{
	( GrabOrRelease and  /*GrabbedInOrder*/


(

 all pre: State - so/last | 
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.holds), have = p.(post.(holds+waits)) |
        let grabbed = have - had |
			(some had and some grabbed) => (no grabbed & mo/prevs[had])
and
 all pre: State - so/last | 
	all p:Process|
     let post = so/next[pre] |
        let had = p.(pre.waits), have = p.(post.(waits)) |
        let grabbed = have - had |
			(some had and some grabbed) => (no grabbed & mo/prevs[had])
)

) <=> GrabOrReleaseActualFix
//	( GrabOrRelease and  GrabbedInOrder) => GrabOrReleaseActualFix
// GrabOrReleaseActualFix =>( GrabOrRelease and  GrabbedInOrder) 

//( GrabOrRelease and GrabbedInOrderSome) =>( GrabOrRelease and  GrabbedInOrder) 
//( GrabOrRelease and  GrabbedInOrder) => ( GrabOrRelease and GrabbedInOrderSome)

}


pred ShowDijkstra  {
//	Initial[so/first] && some (Process.((so/next[so/first]).holds) - Process.((so/first).holds))
//no holds &&	
	(some Process) and GrabOrRelease and  GrabbedInOrder and not GrabbedInOrderIncorrect //and !Deadlock //and # Process =2

			
}

check DijkstraPreventsDeadlocks for 5 State, 5 Process, 4 Mutex //expect 0




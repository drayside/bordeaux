open util/ordering [State] as so
open util/ordering [Mutex] as mo

sig Process {}
sig Mutex {}

sig State { holds, waits: Process -> Mutex }


pred Initial [s: State]  { no s.holds + s.waits }


pred GrabbedInOrder  {
   all pre: State - so/last |
     let post = so/next[pre] |
        let had = Process.(pre.holds), have = Process.(post.holds) |
        let grabbed = have - had |
           some grabbed => grabbed in mo/nexts[had]
}



pred specAndSomeHolds{
	Initial[so/first]
	GrabbedInOrder  
	some holds
}

pred Rest{
	Initial[so/first]
	some holds
}

pred Rest2{
	Initial[so/first]
}

run Rest for 5 State, 5 Process, 4 Mutex

run Rest2 for 5 State, 5 Process, 4 Mutex

run GrabbedInOrder for 5 State, 5 Process, 4 Mutex

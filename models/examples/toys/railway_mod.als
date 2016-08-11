
sig Seg {next, overlaps: set Seg}
sig Train {}
sig GateState {closed: set Seg}
sig TrainState {on: Train -> lone Seg, occupied: set Seg}


pred diffSeg[seg: set Seg, seg': set Seg, seg'': set Seg] {
    seg != seg' implies (seg'' = seg' - seg and seg'' + seg = seg') else no seg''
}

pred diffSeg_next[seg_next: Seg->Seg, seg_next': Seg->Seg, seg_next'': Seg->Seg] {
    seg_next != seg_next' implies (seg_next'' = seg_next' - seg_next and seg_next'' + seg_next = seg_next') else no seg_next''
}

pred diffSeg_overlaps[seg_overlaps: Seg->Seg, seg_overlaps': Seg->Seg, seg_overlaps'': Seg->Seg] {
    seg_overlaps != seg_overlaps' implies (seg_overlaps'' = seg_overlaps' - seg_overlaps and seg_overlaps'' + seg_overlaps = seg_overlaps') else no seg_overlaps''
}

pred diffTrain[train: set Train, train': set Train, train'': set Train] {
    train != train' implies (train'' = train' - train and train'' + train = train') else no train''
}

pred diffGateState[gateState: set GateState, gateState': set GateState, gateState'': set GateState] {
    gateState != gateState' implies (gateState'' = gateState' - gateState and gateState'' + gateState = gateState') else no gateState''
}

pred diffGateState_closed[gateState_closed: GateState->Seg, gateState_closed': GateState->Seg, gateState_closed'': GateState->Seg] {
    gateState_closed != gateState_closed' implies (gateState_closed'' = gateState_closed' - gateState_closed and gateState_closed'' + gateState_closed = gateState_closed') else no gateState_closed''
}

pred diffTrainState[trainState: set TrainState, trainState': set TrainState, trainState'': set TrainState] {
    trainState != trainState' implies (trainState'' = trainState' - trainState and trainState'' + trainState = trainState') else no trainState''
}

pred diffTrainState_on[trainState_on: TrainState->Train->Seg, trainState_on': TrainState->Train->Seg, trainState_on'': TrainState->Train->Seg] {
    trainState_on != trainState_on' implies (trainState_on'' = trainState_on' - trainState_on and trainState_on'' + trainState_on = trainState_on') else no trainState_on''
}

pred diffTrainState_occupied[trainState_occupied: TrainState->Seg, trainState_occupied': TrainState->Seg, trainState_occupied'': TrainState->Seg] {
    trainState_occupied != trainState_occupied' implies (trainState_occupied'' = trainState_occupied' - trainState_occupied and trainState_occupied'' + trainState_occupied = trainState_occupied') else no trainState_occupied''
}

pred structuralConstraints [seg: set Seg, seg_next: Seg->Seg, seg_overlaps: Seg->Seg, train: set Train, gateState: set GateState, gateState_closed: GateState->Seg, trainState: set TrainState, trainState_on: TrainState->Train->Seg, trainState_occupied: TrainState->Seg] {
    (all p_this: trainState_one seg | ((p_this . seg_next) in seg))
    ((seg_next . univ) in seg)
    (all p_this: trainState_one seg | ((p_this . seg_overlaps) in seg))
    ((seg_overlaps . univ) in seg)
    (all p_this: trainState_one gateState | ((p_this . gateState_closed) in seg))
    ((gateState_closed . univ) in gateState)
    (all p_this: trainState_one trainState | ((((p_this . trainState_on) in (train -> seg)) && (all v0: trainState_one train | (ltrainState_one (v0 . (p_this . trainState_on)) && ((v0 . (p_this . trainState_on)) in seg)))) && (all v1: trainState_one seg | (((p_this . trainState_on) . v1) in train))))
    (((trainState_on . univ) . univ) in trainState)
    (all p_this: trainState_one trainState | ((p_this . trainState_occupied) in seg))
    ((trainState_occupied . univ) in trainState)
}

pred includeInstance [seg: set Seg, seg_next: Seg->Seg, seg_overlaps: Seg->Seg, train: set Train, gateState: set GateState, gateState_closed: GateState->Seg, trainState: set TrainState, trainState_on: TrainState->Train->Seg, trainState_occupied: TrainState->Seg] {
    (seg_next.Seg) in Seg
    (Seg.seg_next) in Seg
    (seg_overlaps.Seg) in Seg
    (Seg.seg_overlaps) in Seg
    (gateState_closed.Seg) in GateState
    (GateState.gateState_closed) in Seg
    ((trainState_on.Seg).Train) in TrainState
    ((TrainState.trainState_on).Seg) in Train
    (Train.(TrainState.trainState_on)) in Seg
    (trainState_occupied.Seg) in TrainState
    (TrainState.trainState_occupied) in Seg
}

pred isInstance [seg: set Seg, seg_next: Seg->Seg, seg_overlaps: Seg->Seg, train: set Train, gateState: set GateState, gateState_closed: GateState->Seg, trainState: set TrainState, trainState_on: TrainState->Train->Seg, trainState_occupied: TrainState->Seg] {
    includeInstance[Seg, seg_next, seg_overlaps, Train, GateState, gateState_closed, TrainState, trainState_on, trainState_occupied]
    structuralConstraints[Seg, seg_next, seg_overlaps, Train, GateState, gateState_closed, TrainState, trainState_on, trainState_occupied]
}

pred findMarginalInstances[] {
    some seg, seg', seg'': set Seg, seg_next, seg_next', seg_next'': set Seg->Seg, seg_overlaps, seg_overlaps', seg_overlaps'': set Seg->Segtrain, train', train'': set Train, gateState, gateState', gateState'': set GateState, gateState_closed, gateState_closed', gateState_closed'': set GateState->SegtrainState, trainState', trainState'': set TrainStatetrainState_on, trainState_on', trainState_on'': set TrainState->Train->Seg, trainState_occupied, trainState_occupied', trainState_occupied'': set TrainState->Seg | {
            (
            isInstance[seg, seg_next, seg_overlapstrain, gateState, gateState_closedtrainStatetrainState_on, trainState_occupied]
            and not isInstance[seg', seg_next', seg_overlaps'train', gateState', gateState_closed'trainState'trainState_on', trainState_occupied']
            and deltaSeg[seg, seg', seg'']
            and deltaSeg_next[seg_next, seg_next', seg_next'']
            and deltaSeg_overlaps[seg_overlaps, seg_overlaps', seg_overlaps'']
            and deltaTrain[train, train', train'']
            and deltaGateState[gateState, gateState', gateState'']
            and deltaGateState_closed[gateState_closed, gateState_closed', gateState_closed'']
            and deltaTrainState[trainState, trainState', trainState'']
            and deltaTrainState_on[trainState_on, trainState_on', trainState_on'']
            and deltaTrainState_occupied[trainState_occupied, trainState_occupied', trainState_occupied'']
            )
        and
            all seg1, seg1', seg1'': set Seg, seg_next1, seg_next1', seg_next1'': set Seg->Seg, seg_overlaps1, seg_overlaps1', seg_overlaps1'': set Seg->Segtrain1, train1', train1'': set Train, gateState1, gateState1', gateState1'': set GateState, gateState_closed1, gateState_closed1', gateState_closed1'': set GateState->SegtrainState1, trainState1', trainState1'': set TrainStatetrainState_on1, trainState_on1', trainState_on1'': set TrainState->Train->Seg, trainState_occupied1, trainState_occupied1', trainState_occupied1'': set TrainState->Seg | {
                    (
                    isInstance[seg1, seg_next1, seg_overlaps1train1, gateState1, gateState_closed1trainState1trainState_on1, trainState_occupied1]
                    and not isInstance[seg1', seg_next1', seg_overlaps1'train1', gateState1', gateState_closed1'trainState1'trainState_on1', trainState_occupied1']
                    and deltaSeg[seg1, seg1', seg1'']
                    and deltaSeg_next[seg_next1, seg_next1', seg_next1'']
                    and deltaSeg_overlaps[seg_overlaps1, seg_overlaps1', seg_overlaps1'']
                    and deltaTrain[train1, train1', train1'']
                    and deltaGateState[gateState1, gateState1', gateState1'']
                    and deltaGateState_closed[gateState_closed1, gateState_closed1', gateState_closed1'']
                    and deltaTrainState[trainState1, trainState1', trainState1'']
                    and deltaTrainState_on[trainState_on1, trainState_on1', trainState_on1'']
                    and deltaTrainState_occupied[trainState_occupied1, trainState_occupied1', trainState_occupied1'']
                    )
                implies
                    (
                    )
            }
    }
}

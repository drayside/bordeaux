module AutoSoft

sig RoadSegment {}
sig Driver {}
abstract sig MapObject {}
abstract sig RoadObject extends MapObject {}
sig Lane extends MapObject {}
sig AutoSoftCar extends RoadObject {}
sig Drives {}
sig IsOn {}
sig AutoSoft {}
sig BDS {}
sig CC {}
sig HC {}
sig HP {}
sig FCA {}
sig SLC {}
sig Coord {}
sig Shape {}
sig Angle {}
sig IgnitionState {}
sig SpeedLim {}
sig IntRange {}

sig WS {
    RoadSegments : set RoadSegment,
    Drivers : set Driver,
    MapObjects : set MapObject,
    RoadObjects : set RoadObject,
    Lanes : set Lane,
    AutoSoftCars : set AutoSoftCar,
    Drivess : set Drives,
    IsOns : set IsOn,
    AutoSofts : set AutoSoft,
    BDSs : set BDS,
    CCs : set CC,
    HCs : set HC,
    HPs : set HP,
    FCAs : set FCA,
    SLCs : set SLC,
    RoadSegment_speedLimit : RoadSegments-> SpeedLim,
    MapObject_position : MapObjects-> Coord,
    MapObject_shape : MapObjects-> Shape,
    RoadObject_acceleration : RoadObjects-> IntRange,
    RoadObject_speed : RoadObjects-> IntRange,
    AutoSoftCar_steerDirection : AutoSoftCars-> Angle,
    AutoSoftCar_ignition : AutoSoftCars-> IgnitionState,
    Drives_r1 : Drivess-> one Drivers,
    Drives_r2 : Drivess-> one AutoSoftCars,
    IsOn_r1 : IsOns-> one RoadSegments,
    IsOn_r2 : IsOns-> one Lanes,
    AutoSoft_BDS : AutoSofts one->one BDSs,
    CC_goalAccel : CCs-> IntRange,
    CC_cruiseSpeed : CCs-> IntRange,
    AutoSoft_CC : AutoSofts one->one CCs,
    HC_headway : HCs-> IntRange,
    AutoSoft_HC : AutoSofts one->one HCs,
    AutoSoft_HP : AutoSofts one->one HPs,
    FCA_alertLevel : FCAs-> IntRange,
    AutoSoft_FCA : AutoSofts one->one FCAs,
    AutoSoft_SLC : AutoSofts one->one SLCs,
} {
    all o : RoadSegments | # (o.RoadSegment_speedLimit) = 1
    all o : MapObjects | # (o.MapObject_shape) = 1
    all o : MapObjects | # (o.MapObject_position) = 1
    all o : RoadObjects | # (o.RoadObject_speed) = 1
    all o : RoadObjects | # (o.RoadObject_acceleration) = 1
    all o : AutoSoftCars | # (o.AutoSoftCar_ignition) = 1
    all o : AutoSoftCars | # (o.AutoSoftCar_steerDirection) = 1
    all o : CCs | # (o.CC_cruiseSpeed) = 1
    all o : CCs | # (o.CC_goalAccel) = 1
    all o : HCs | # (o.HC_headway) = 1
    all o : FCAs | # (o.FCA_alertLevel) = 1
}
pred distinct_valid_WSs {
    all ws, ws1 : WS | (ws.RoadSegments = ws1.RoadSegments and ws.RoadSegment_speedLimit = ws1.RoadSegment_speedLimit and ws.Drivers = ws1.Drivers and ws.MapObjects = ws1.MapObjects and ws.MapObject_position = ws1.MapObject_position and ws.MapObject_shape = ws1.MapObject_shape and ws.RoadObjects = ws1.RoadObjects and ws.RoadObject_acceleration = ws1.RoadObject_acceleration and ws.RoadObject_speed = ws1.RoadObject_speed and ws.Lanes = ws1.Lanes and ws.AutoSoftCars = ws1.AutoSoftCars and ws.AutoSoftCar_steerDirection = ws1.AutoSoftCar_steerDirection and ws.AutoSoftCar_ignition = ws1.AutoSoftCar_ignition and ws.Drivess = ws1.Drivess and ws.Drives_r1 = ws1.Drives_r1 and ws.Drives_r2 = ws1.Drives_r2 and ws.IsOns = ws1.IsOns and ws.IsOn_r1 = ws1.IsOn_r1 and ws.IsOn_r2 = ws1.IsOn_r2 and ws.AutoSofts = ws1.AutoSofts and ws.BDSs = ws1.BDSs and ws.CCs = ws1.CCs and ws.CC_goalAccel = ws1.CC_goalAccel and ws.CC_cruiseSpeed = ws1.CC_cruiseSpeed and ws.HCs = ws1.HCs and ws.HC_headway = ws1.HC_headway and ws.HPs = ws1.HPs and ws.FCAs = ws1.FCAs and ws.FCA_alertLevel = ws1.FCA_alertLevel and ws.SLCs = ws1.SLCs) implies ws = ws1  
    all ws : WS | WSC [ws]
}
pred WSC (ws : WS) {
    (ws.RoadObjects = ws.MapObjects & RoadObject)
    (ws.Lanes = ws.MapObjects & Lane)
    (ws.AutoSoftCars = ws.RoadObjects & AutoSoftCar)
    (all autosoftcar : ws.AutoSoftCars | # ((((ws.Drives_r2).autosoftcar)).(ws.Drives_r1)) = 1)
    (all driver : ws.Drivers | # ((((ws.Drives_r1).driver)).(ws.Drives_r2)) = 1)
    (all lane : ws.Lanes | # ((((ws.IsOn_r2).lane)).(ws.IsOn_r1)) = 1)
    (all roadsegment : ws.RoadSegments | # ((((ws.IsOn_r1).roadsegment)).(ws.IsOn_r2)) >= 1)
    (ws.MapObjects = ws.Lanes + ws.RoadObjects)
}
pred WSTC (wsPre, ws : WS) {
    (all o : wsPre.Lanes & ws.Lanes | wsPre.IsOn_r2.o.(wsPre.IsOn_r1) = ws.IsOn_r2.o.(ws.IsOn_r1))
    (wsPre.AutoSoft_BDS = ws.AutoSoft_BDS)
    (wsPre.AutoSoft_CC = ws.AutoSoft_CC)
    (wsPre.AutoSoft_HC = ws.AutoSoft_HC)
    (wsPre.AutoSoft_HP = ws.AutoSoft_HP)
    (wsPre.AutoSoft_FCA = ws.AutoSoft_FCA)
    (wsPre.AutoSoft_SLC = ws.AutoSoft_SLC)
}
enum Bool {true, false}
enum AutoSoft_BDS_main_STATES {AutoSoft_BDS_main_on, AutoSoft_BDS_main_off}
pred remove_RoadSegment (wsPre, wsPost : WS, o1 : RoadSegment) {
    o1 in wsPre.RoadSegments implies
    o1 not in wsPost.RoadSegments
}
pred add_RoadSegment (wsPre, wsPost : WS, o1 : RoadSegment) {
    o1 not in wsPre.RoadSegments implies
    o1 in wsPost.RoadSegments
}
pred change_RoadSegment_speedLimit (wsPre, wsPost : WS, o1 : RoadSegment, v1 : SpeedLim) {
    o1 in wsPre.RoadSegments implies
    o1.(wsPost.RoadSegment_speedLimit) = v1
}
pred remove_Driver (wsPre, wsPost : WS, o1 : Driver) {
    o1 in wsPre.Drivers implies
    o1 not in wsPost.Drivers
}
pred add_Driver (wsPre, wsPost : WS, o1 : Driver) {
    o1 not in wsPre.Drivers implies
    o1 in wsPost.Drivers
}
pred remove_MapObject (wsPre, wsPost : WS, o1 : MapObject) {
    o1 in wsPre.MapObjects implies
    o1 not in wsPost.MapObjects
}
pred add_MapObject (wsPre, wsPost : WS, o1 : MapObject) {
    o1 not in wsPre.MapObjects implies
    o1 in wsPost.MapObjects
}
pred change_MapObject_shape (wsPre, wsPost : WS, o1 : MapObject, v1 : Shape) {
    o1 in wsPre.MapObjects implies
    o1.(wsPost.MapObject_shape) = v1
}
pred change_MapObject_position (wsPre, wsPost : WS, o1 : MapObject, v1 : Coord) {
    o1 in wsPre.MapObjects implies
    o1.(wsPost.MapObject_position) = v1
}
pred remove_RoadObject (wsPre, wsPost : WS, o1 : RoadObject) {
    o1 in wsPre.RoadObjects implies
    o1 not in wsPost.RoadObjects
}
pred add_RoadObject (wsPre, wsPost : WS, o1 : RoadObject) {
    o1 not in wsPre.RoadObjects implies
    o1 in wsPost.RoadObjects
}
pred change_RoadObject_speed (wsPre, wsPost : WS, o1 : RoadObject, v1 : IntRange) {
    o1 in wsPre.RoadObjects implies
    o1.(wsPost.RoadObject_speed) = v1
}
pred change_RoadObject_acceleration (wsPre, wsPost : WS, o1 : RoadObject, v1 : IntRange) {
    o1 in wsPre.RoadObjects implies
    o1.(wsPost.RoadObject_acceleration) = v1
}
pred remove_Lane (wsPre, wsPost : WS, o1 : Lane) {
    o1 in wsPre.Lanes implies
    o1 not in wsPost.Lanes
}
pred add_Lane (wsPre, wsPost : WS, o1 : Lane) {
    o1 not in wsPre.Lanes implies
    o1 in wsPost.Lanes
}
pred remove_AutoSoftCar (wsPre, wsPost : WS, o1 : AutoSoftCar) {
    o1 in wsPre.AutoSoftCars implies
    o1 not in wsPost.AutoSoftCars
}
pred add_AutoSoftCar (wsPre, wsPost : WS, o1 : AutoSoftCar) {
    o1 not in wsPre.AutoSoftCars implies
    o1 in wsPost.AutoSoftCars
}
pred change_AutoSoftCar_ignition (wsPre, wsPost : WS, o1 : AutoSoftCar, v1 : IgnitionState) {
    o1 in wsPre.AutoSoftCars implies
    o1.(wsPost.AutoSoftCar_ignition) = v1
}
pred change_AutoSoftCar_steerDirection (wsPre, wsPost : WS, o1 : AutoSoftCar, v1 : Angle) {
    o1 in wsPre.AutoSoftCars implies
    o1.(wsPost.AutoSoftCar_steerDirection) = v1
}
pred remove_Drives (wsPre, wsPost : WS, o1 : Drives) {
    o1 in wsPre.Drivess implies
    o1 not in wsPost.Drivess
}
pred add_Drives (wsPre, wsPost : WS, o1 : Drives) {
    o1 not in wsPre.Drivess implies
    o1 in wsPost.Drivess
}
pred remove_IsOn (wsPre, wsPost : WS, o1 : IsOn) {
    o1 in wsPre.IsOns implies
    o1 not in wsPost.IsOns
}
pred add_IsOn (wsPre, wsPost : WS, o1 : IsOn) {
    o1 not in wsPre.IsOns implies
    o1 in wsPost.IsOns
}
pred remove_AutoSoft (wsPre, wsPost : WS, o1 : AutoSoft) {
    o1 in wsPre.AutoSofts implies
    o1 not in wsPost.AutoSofts
}
pred add_AutoSoft (wsPre, wsPost : WS, o1 : AutoSoft) {
    o1 not in wsPre.AutoSofts implies
    o1 in wsPost.AutoSofts
}
pred remove_BDS (wsPre, wsPost : WS, o1 : BDS) {
    o1 in wsPre.BDSs implies
    o1 not in wsPost.BDSs
}
pred add_BDS (wsPre, wsPost : WS, o1 : BDS) {
    o1 not in wsPre.BDSs implies
    o1 in wsPost.BDSs
}
pred remove_CC (wsPre, wsPost : WS, o1 : CC) {
    o1 in wsPre.CCs implies
    o1 not in wsPost.CCs
}
pred add_CC (wsPre, wsPost : WS, o1 : CC) {
    o1 not in wsPre.CCs implies
    o1 in wsPost.CCs
}
pred change_CC_cruiseSpeed (wsPre, wsPost : WS, o1 : CC, v1 : IntRange) {
    o1 in wsPre.CCs implies
    o1.(wsPost.CC_cruiseSpeed) = v1
}
pred change_CC_goalAccel (wsPre, wsPost : WS, o1 : CC, v1 : IntRange) {
    o1 in wsPre.CCs implies
    o1.(wsPost.CC_goalAccel) = v1
}
pred remove_HC (wsPre, wsPost : WS, o1 : HC) {
    o1 in wsPre.HCs implies
    o1 not in wsPost.HCs
}
pred add_HC (wsPre, wsPost : WS, o1 : HC) {
    o1 not in wsPre.HCs implies
    o1 in wsPost.HCs
}
pred change_HC_headway (wsPre, wsPost : WS, o1 : HC, v1 : IntRange) {
    o1 in wsPre.HCs implies
    o1.(wsPost.HC_headway) = v1
}
pred remove_HP (wsPre, wsPost : WS, o1 : HP) {
    o1 in wsPre.HPs implies
    o1 not in wsPost.HPs
}
pred add_HP (wsPre, wsPost : WS, o1 : HP) {
    o1 not in wsPre.HPs implies
    o1 in wsPost.HPs
}
pred remove_FCA (wsPre, wsPost : WS, o1 : FCA) {
    o1 in wsPre.FCAs implies
    o1 not in wsPost.FCAs
}
pred add_FCA (wsPre, wsPost : WS, o1 : FCA) {
    o1 not in wsPre.FCAs implies
    o1 in wsPost.FCAs
}
pred change_FCA_alertLevel (wsPre, wsPost : WS, o1 : FCA, v1 : IntRange) {
    o1 in wsPre.FCAs implies
    o1.(wsPost.FCA_alertLevel) = v1
}
pred remove_SLC (wsPre, wsPost : WS, o1 : SLC) {
    o1 in wsPre.SLCs implies
    o1 not in wsPost.SLCs
}
pred add_SLC (wsPre, wsPost : WS, o1 : SLC) {
    o1 not in wsPre.SLCs implies
    o1 in wsPost.SLCs
}
pred AutoSoft_BDS_main_t1 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_t2 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_acceleration_t3 (wsPre, wsPost : WS, a1_v1 : IntRange, a1_o1 : AutoSoftCar) {
    change_RoadObject_acceleration [wsPre, wsPost, a1_o1, a1_v1]
}
pred AutoSoft_BDS_main_on_deceleration_t4 (wsPre, wsPost : WS, a1_v1 : IntRange, a1_o1 : AutoSoftCar) {
    change_RoadObject_acceleration [wsPre, wsPost, a1_o1, a1_v1]
}
pred AutoSoft_BDS_main_on_steering_t5 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_t1 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_t2 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_t3 (wsPre, wsPost : WS, a2_v1 : IntRange, a2_o1 : CC, a1_v1 : IntRange, a1_o1 : CC) {
    change_CC_cruiseSpeed [wsPre, wsPost, a1_o1, a1_v1]
    change_CC_goalAccel [wsPre, wsPost, a2_o1, a2_v1]
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_t4 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_t5 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 (wsPre, wsPost : WS, a2_v1 : IntRange, a2_o1 : CC, a1_v1 : IntRange, a1_o1 : AutoSoftCar) {
    change_RoadObject_acceleration [wsPre, wsPost, a1_o1, a1_v1]
    change_CC_goalAccel [wsPre, wsPost, a2_o1, a2_v1]
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 (wsPre, wsPost : WS, a1_v1 : IntRange, a1_o1 : CC) {
    change_CC_cruiseSpeed [wsPre, wsPost, a1_o1, a1_v1]
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 (wsPre, wsPost : WS, a1_v1 : IntRange, a1_o1 : HC) {
    change_HC_headway [wsPre, wsPost, a1_o1, a1_v1]
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 (wsPre, wsPost : WS, a2_v1 : IntRange, a2_o1 : CC, a1_v1 : IntRange, a1_o1 : AutoSoftCar) {
    change_RoadObject_acceleration [wsPre, wsPost, a1_o1, a1_v1]
    change_CC_goalAccel [wsPre, wsPost, a2_o1, a2_v1]
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 (wsPre, wsPost : WS, a1_v1 : IntRange, a1_o1 : HC) {
    change_HC_headway [wsPre, wsPost, a1_o1, a1_v1]
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 (wsPre, wsPost : WS, a1_v1 : IntRange, a1_o1 : HC) {
    change_HC_headway [wsPre, wsPost, a1_o1, a1_v1]
}
pred AutoSoft_BDS_main_on_CC_main_FCA_main_t1 (wsPre, wsPost : WS, a1_v1 : IntRange, a1_o1 : FCA) {
    change_FCA_alertLevel [wsPre, wsPost, a1_o1, a1_v1]
}
pred AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 (wsPre, wsPost : WS, a1_v1 : IntRange, a1_o1 : FCA) {
    change_FCA_alertLevel [wsPre, wsPost, a1_o1, a1_v1]
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 (wsPre, wsPost : WS) {
}
pred AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 (wsPre, wsPost : WS, a2_v1 : IntRange, a2_o1 : CC, a1_v1 : IntRange, a1_o1 : AutoSoftCar) {
    change_RoadObject_acceleration [wsPre, wsPost, a1_o1, a1_v1]
    change_CC_goalAccel [wsPre, wsPost, a2_o1, a2_v1]
}
//run distinct_valid_WSs for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 2 IntRange, exactly 169 WS
//check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 2 IntRange, exactly 169 WS


inst i {
RoadSegment = RoadSegment0,
Driver = Driver0,
MapObject = AutoSoftCar0 + Lane0,
RoadObject = AutoSoftCar0,
AutoSoftCar = AutoSoftCar0,
Lane = Lane0,
Drives = Drives0,
IsOn = IsOn0,
AutoSoft = AutoSoft0,
BDS = BDS0,
CC = CC0,
HC = HC0,
HP = HP0,
FCA = FCA0,
SLC = SLC0,
Coord = Coord0,
Shape = Shape0,
Angle = Angle0,
IgnitionState = IgnitionState0,
SpeedLim = SpeedLim0,
IntRange = IntRange0 + IntRange1,
exactly 450 WS
}

run distinct_valid_WSs for i

assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_steering_t5 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_1 : IntRange, a1_o1_1 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_1, a1_o1_1]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_2 : IntRange, a1_o1_2 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_2, a1_o1_2]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_3 : IntRange, a1_o1_3 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_3, a1_o1_3]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_1 : IntRange, a2_o1_1 : CC, a1_v1_4 : IntRange, a1_o1_4 : CC, a1_v1_5 : IntRange, a1_o1_5 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t3 [wsPre, wsPost, a2_v1_1, a2_o1_1, a1_v1_4, a1_o1_4] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_5, a1_o1_5]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_6 : IntRange, a1_o1_6 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t4 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_6, a1_o1_6]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_7 : IntRange, a1_o1_7 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t5 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_7, a1_o1_7]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_2 : IntRange, a2_o1_2 : CC, a1_v1_8 : IntRange, a1_o1_8 : AutoSoftCar, a1_v1_9 : IntRange, a1_o1_9 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_2, a2_o1_2, a1_v1_8, a1_o1_8] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_9, a1_o1_9]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_10 : IntRange, a1_o1_10 : CC, a1_v1_11 : IntRange, a1_o1_11 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_10, a1_o1_10] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_11, a1_o1_11]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_12 : IntRange, a1_o1_12 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_12, a1_o1_12]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_13 : IntRange, a1_o1_13 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_13, a1_o1_13]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_14 : IntRange, a1_o1_14 : HC, a1_v1_15 : IntRange, a1_o1_15 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_14, a1_o1_14] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_15, a1_o1_15]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_3 : IntRange, a2_o1_3 : CC, a1_v1_16 : IntRange, a1_o1_16 : AutoSoftCar, a1_v1_17 : IntRange, a1_o1_17 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_3, a2_o1_3, a1_v1_16, a1_o1_16] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_17, a1_o1_17]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_18 : IntRange, a1_o1_18 : HC, a1_v1_19 : IntRange, a1_o1_19 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_18, a1_o1_18] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_19, a1_o1_19]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_20 : IntRange, a1_o1_20 : HC, a1_v1_21 : IntRange, a1_o1_21 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_20, a1_o1_20] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_21, a1_o1_21]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_22 : IntRange, a1_o1_22 : FCA, a1_v1_23 : IntRange, a1_o1_23 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_22, a1_o1_22] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_23, a1_o1_23]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_24 : IntRange, a1_o1_24 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_24, a1_o1_24]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_25 : IntRange, a1_o1_25 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_25, a1_o1_25]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_26 : IntRange, a1_o1_26 : FCA, a1_v1_27 : IntRange, a1_o1_27 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_26, a1_o1_26] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_27, a1_o1_27]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_28 : IntRange, a1_o1_28 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_28, a1_o1_28]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_29 : IntRange, a1_o1_29 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_29, a1_o1_29]
}
assert AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_4 : IntRange, a2_o1_4 : CC, a1_v1_30 : IntRange, a1_o1_30 : AutoSoftCar, a1_v1_31 : IntRange, a1_o1_31 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_4, a2_o1_4, a1_v1_30, a1_o1_30] and AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1_31, a1_o1_31]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_steering_t5 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_32 : IntRange, a1_o1_32 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_32, a1_o1_32]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_33 : IntRange, a1_o1_33 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_33, a1_o1_33]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_34 : IntRange, a1_o1_34 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_34, a1_o1_34]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_5 : IntRange, a2_o1_5 : CC, a1_v1_35 : IntRange, a1_o1_35 : CC, a1_v1_36 : IntRange, a1_o1_36 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t3 [wsPre, wsPost, a2_v1_5, a2_o1_5, a1_v1_35, a1_o1_35] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_36, a1_o1_36]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_37 : IntRange, a1_o1_37 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t4 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_37, a1_o1_37]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_38 : IntRange, a1_o1_38 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t5 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_38, a1_o1_38]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_6 : IntRange, a2_o1_6 : CC, a1_v1_39 : IntRange, a1_o1_39 : AutoSoftCar, a1_v1_40 : IntRange, a1_o1_40 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_6, a2_o1_6, a1_v1_39, a1_o1_39] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_40, a1_o1_40]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_41 : IntRange, a1_o1_41 : CC, a1_v1_42 : IntRange, a1_o1_42 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_41, a1_o1_41] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_42, a1_o1_42]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_43 : IntRange, a1_o1_43 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_43, a1_o1_43]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_44 : IntRange, a1_o1_44 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_44, a1_o1_44]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_45 : IntRange, a1_o1_45 : HC, a1_v1_46 : IntRange, a1_o1_46 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_45, a1_o1_45] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_46, a1_o1_46]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_7 : IntRange, a2_o1_7 : CC, a1_v1_47 : IntRange, a1_o1_47 : AutoSoftCar, a1_v1_48 : IntRange, a1_o1_48 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_7, a2_o1_7, a1_v1_47, a1_o1_47] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_48, a1_o1_48]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_49 : IntRange, a1_o1_49 : HC, a1_v1_50 : IntRange, a1_o1_50 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_49, a1_o1_49] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_50, a1_o1_50]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_51 : IntRange, a1_o1_51 : HC, a1_v1_52 : IntRange, a1_o1_52 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_51, a1_o1_51] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_52, a1_o1_52]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_53 : IntRange, a1_o1_53 : FCA, a1_v1_54 : IntRange, a1_o1_54 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_53, a1_o1_53] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_54, a1_o1_54]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_55 : IntRange, a1_o1_55 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_55, a1_o1_55]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_56 : IntRange, a1_o1_56 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_56, a1_o1_56]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_57 : IntRange, a1_o1_57 : FCA, a1_v1_58 : IntRange, a1_o1_58 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_57, a1_o1_57] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_58, a1_o1_58]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_59 : IntRange, a1_o1_59 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_59, a1_o1_59]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_60 : IntRange, a1_o1_60 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_60, a1_o1_60]
}
assert AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_8 : IntRange, a2_o1_8 : CC, a1_v1_61 : IntRange, a1_o1_61 : AutoSoftCar, a1_v1_62 : IntRange, a1_o1_62 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_8, a2_o1_8, a1_v1_61, a1_o1_61] and AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1_62, a1_o1_62]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_9 : IntRange, a2_o1_9 : CC, a1_v1_63 : IntRange, a1_o1_63 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t3 [wsPre, wsPost, a2_v1_9, a2_o1_9, a1_v1_63, a1_o1_63] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t4 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t5 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_10 : IntRange, a2_o1_10 : CC, a1_v1_64 : IntRange, a1_o1_64 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_10, a2_o1_10, a1_v1_64, a1_o1_64] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_65 : IntRange, a1_o1_65 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_65, a1_o1_65] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_66 : IntRange, a1_o1_66 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_66, a1_o1_66] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_11 : IntRange, a2_o1_11 : CC, a1_v1_67 : IntRange, a1_o1_67 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_11, a2_o1_11, a1_v1_67, a1_o1_67] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_68 : IntRange, a1_o1_68 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_68, a1_o1_68] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_69 : IntRange, a1_o1_69 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_69, a1_o1_69] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_70 : IntRange, a1_o1_70 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_70, a1_o1_70] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_71 : IntRange, a1_o1_71 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_71, a1_o1_71] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_12 : IntRange, a2_o1_12 : CC, a1_v1_72 : IntRange, a1_o1_72 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_12, a2_o1_12, a1_v1_72, a1_o1_72] and AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_73 : IntRange, a1_o1_73 : FCA, a2_v1_13 : IntRange, a2_o1_13 : CC, a1_v1_74 : IntRange, a1_o1_74 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_73, a1_o1_73] and AutoSoft_BDS_main_on_CC_main_enabled_main_t3 [wsPre, wsPost, a2_v1_13, a2_o1_13, a1_v1_74, a1_o1_74]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_14 : IntRange, a2_o1_14 : CC, a1_v1_75 : IntRange, a1_o1_75 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_t3 [wsPre, wsPost, a2_v1_14, a2_o1_14, a1_v1_75, a1_o1_75]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_15 : IntRange, a2_o1_15 : CC, a1_v1_76 : IntRange, a1_o1_76 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_t3 [wsPre, wsPost, a2_v1_15, a2_o1_15, a1_v1_76, a1_o1_76]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_77 : IntRange, a1_o1_77 : FCA, a2_v1_16 : IntRange, a2_o1_16 : CC, a1_v1_78 : IntRange, a1_o1_78 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_77, a1_o1_77] and AutoSoft_BDS_main_on_CC_main_enabled_main_t3 [wsPre, wsPost, a2_v1_16, a2_o1_16, a1_v1_78, a1_o1_78]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_79 : IntRange, a1_o1_79 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_79, a1_o1_79] and AutoSoft_BDS_main_on_CC_main_enabled_main_t4 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_t4 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_t4 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_80 : IntRange, a1_o1_80 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_80, a1_o1_80] and AutoSoft_BDS_main_on_CC_main_enabled_main_t4 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_81 : IntRange, a1_o1_81 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_81, a1_o1_81] and AutoSoft_BDS_main_on_CC_main_enabled_main_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_82 : IntRange, a1_o1_82 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_82, a1_o1_82] and AutoSoft_BDS_main_on_CC_main_enabled_main_t5 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_83 : IntRange, a1_o1_83 : HC, a2_v1_17 : IntRange, a2_o1_17 : CC, a1_v1_84 : IntRange, a1_o1_84 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_83, a1_o1_83] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_17, a2_o1_17, a1_v1_84, a1_o1_84]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_85 : IntRange, a1_o1_85 : HC, a2_v1_18 : IntRange, a2_o1_18 : CC, a1_v1_86 : IntRange, a1_o1_86 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_85, a1_o1_85] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_18, a2_o1_18, a1_v1_86, a1_o1_86]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_87 : IntRange, a1_o1_87 : HC, a2_v1_19 : IntRange, a2_o1_19 : CC, a1_v1_88 : IntRange, a1_o1_88 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_87, a1_o1_87] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_19, a2_o1_19, a1_v1_88, a1_o1_88]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_89 : IntRange, a1_o1_89 : FCA, a2_v1_20 : IntRange, a2_o1_20 : CC, a1_v1_90 : IntRange, a1_o1_90 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_89, a1_o1_89] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_20, a2_o1_20, a1_v1_90, a1_o1_90]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_21 : IntRange, a2_o1_21 : CC, a1_v1_91 : IntRange, a1_o1_91 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_21, a2_o1_21, a1_v1_91, a1_o1_91]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_22 : IntRange, a2_o1_22 : CC, a1_v1_92 : IntRange, a1_o1_92 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_22, a2_o1_22, a1_v1_92, a1_o1_92]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_93 : IntRange, a1_o1_93 : FCA, a2_v1_23 : IntRange, a2_o1_23 : CC, a1_v1_94 : IntRange, a1_o1_94 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_93, a1_o1_93] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_23, a2_o1_23, a1_v1_94, a1_o1_94]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_24 : IntRange, a2_o1_24 : CC, a1_v1_95 : IntRange, a1_o1_95 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_24, a2_o1_24, a1_v1_95, a1_o1_95]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_25 : IntRange, a2_o1_25 : CC, a1_v1_96 : IntRange, a1_o1_96 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1_25, a2_o1_25, a1_v1_96, a1_o1_96]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_97 : IntRange, a1_o1_97 : HC, a1_v1_98 : IntRange, a1_o1_98 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_97, a1_o1_97] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_98, a1_o1_98]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_26 : IntRange, a2_o1_26 : CC, a1_v1_99 : IntRange, a1_o1_99 : AutoSoftCar, a1_v1_100 : IntRange, a1_o1_100 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_26, a2_o1_26, a1_v1_99, a1_o1_99] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_100, a1_o1_100]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_101 : IntRange, a1_o1_101 : HC, a1_v1_102 : IntRange, a1_o1_102 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_101, a1_o1_101] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_102, a1_o1_102]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_103 : IntRange, a1_o1_103 : HC, a1_v1_104 : IntRange, a1_o1_104 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_103, a1_o1_103] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_104, a1_o1_104]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_105 : IntRange, a1_o1_105 : FCA, a1_v1_106 : IntRange, a1_o1_106 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_105, a1_o1_105] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_106, a1_o1_106]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_107 : IntRange, a1_o1_107 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_107, a1_o1_107]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_108 : IntRange, a1_o1_108 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_108, a1_o1_108]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_109 : IntRange, a1_o1_109 : FCA, a1_v1_110 : IntRange, a1_o1_110 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_109, a1_o1_109] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_110, a1_o1_110]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_111 : IntRange, a1_o1_111 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_111, a1_o1_111]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_112 : IntRange, a1_o1_112 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_112, a1_o1_112]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_27 : IntRange, a2_o1_27 : CC, a1_v1_113 : IntRange, a1_o1_113 : AutoSoftCar, a1_v1_114 : IntRange, a1_o1_114 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_27, a2_o1_27, a1_v1_113, a1_o1_113] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1_114, a1_o1_114]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_115 : IntRange, a1_o1_115 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_115, a1_o1_115] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_28 : IntRange, a2_o1_28 : CC, a1_v1_116 : IntRange, a1_o1_116 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_28, a2_o1_28, a1_v1_116, a1_o1_116] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_117 : IntRange, a1_o1_117 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_117, a1_o1_117] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_118 : IntRange, a1_o1_118 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_118, a1_o1_118] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_119 : IntRange, a1_o1_119 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_119, a1_o1_119] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_120 : IntRange, a1_o1_120 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_120, a1_o1_120] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_29 : IntRange, a2_o1_29 : CC, a1_v1_121 : IntRange, a1_o1_121 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_29, a2_o1_29, a1_v1_121, a1_o1_121] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_122 : IntRange, a1_o1_122 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_122, a1_o1_122] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_30 : IntRange, a2_o1_30 : CC, a1_v1_123 : IntRange, a1_o1_123 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_30, a2_o1_30, a1_v1_123, a1_o1_123] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_124 : IntRange, a1_o1_124 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_124, a1_o1_124] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_125 : IntRange, a1_o1_125 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_125, a1_o1_125] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_126 : IntRange, a1_o1_126 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_126, a1_o1_126] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_127 : IntRange, a1_o1_127 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_127, a1_o1_127] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_31 : IntRange, a2_o1_31 : CC, a1_v1_128 : IntRange, a1_o1_128 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_31, a2_o1_31, a1_v1_128, a1_o1_128] and AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_129 : IntRange, a1_o1_129 : HC, a1_v1_130 : IntRange, a1_o1_130 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_129, a1_o1_129] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_130, a1_o1_130]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_131 : IntRange, a1_o1_131 : FCA, a1_v1_132 : IntRange, a1_o1_132 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_131, a1_o1_131] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_132, a1_o1_132]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_133 : IntRange, a1_o1_133 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_133, a1_o1_133]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_134 : IntRange, a1_o1_134 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_134, a1_o1_134]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_135 : IntRange, a1_o1_135 : FCA, a1_v1_136 : IntRange, a1_o1_136 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_135, a1_o1_135] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_136, a1_o1_136]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_137 : IntRange, a1_o1_137 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_137, a1_o1_137]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_138 : IntRange, a1_o1_138 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_138, a1_o1_138]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_32 : IntRange, a2_o1_32 : CC, a1_v1_139 : IntRange, a1_o1_139 : AutoSoftCar, a1_v1_140 : IntRange, a1_o1_140 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_32, a2_o1_32, a1_v1_139, a1_o1_139] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1_140, a1_o1_140]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_141 : IntRange, a1_o1_141 : HC, a2_v1_33 : IntRange, a2_o1_33 : CC, a1_v1_142 : IntRange, a1_o1_142 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_141, a1_o1_141] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_33, a2_o1_33, a1_v1_142, a1_o1_142]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_143 : IntRange, a1_o1_143 : FCA, a2_v1_34 : IntRange, a2_o1_34 : CC, a1_v1_144 : IntRange, a1_o1_144 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_143, a1_o1_143] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_34, a2_o1_34, a1_v1_144, a1_o1_144]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_35 : IntRange, a2_o1_35 : CC, a1_v1_145 : IntRange, a1_o1_145 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_35, a2_o1_35, a1_v1_145, a1_o1_145]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_36 : IntRange, a2_o1_36 : CC, a1_v1_146 : IntRange, a1_o1_146 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_36, a2_o1_36, a1_v1_146, a1_o1_146]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_147 : IntRange, a1_o1_147 : FCA, a2_v1_37 : IntRange, a2_o1_37 : CC, a1_v1_148 : IntRange, a1_o1_148 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_147, a1_o1_147] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_37, a2_o1_37, a1_v1_148, a1_o1_148]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_38 : IntRange, a2_o1_38 : CC, a1_v1_149 : IntRange, a1_o1_149 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_38, a2_o1_38, a1_v1_149, a1_o1_149]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_39 : IntRange, a2_o1_39 : CC, a1_v1_150 : IntRange, a1_o1_150 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_39, a2_o1_39, a1_v1_150, a1_o1_150]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_40 : IntRange, a2_o1_40 : CC, a1_v1_151 : IntRange, a1_o1_151 : AutoSoftCar, a2_v1_41 : IntRange, a2_o1_41 : CC, a1_v1_152 : IntRange, a1_o1_152 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_40, a2_o1_40, a1_v1_151, a1_o1_151] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1_41, a2_o1_41, a1_v1_152, a1_o1_152]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_153 : IntRange, a1_o1_153 : HC, a1_v1_154 : IntRange, a1_o1_154 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_153, a1_o1_153] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_154, a1_o1_154]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_155 : IntRange, a1_o1_155 : FCA, a1_v1_156 : IntRange, a1_o1_156 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_155, a1_o1_155] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_156, a1_o1_156]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_157 : IntRange, a1_o1_157 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_157, a1_o1_157]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_158 : IntRange, a1_o1_158 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_158, a1_o1_158]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_159 : IntRange, a1_o1_159 : FCA, a1_v1_160 : IntRange, a1_o1_160 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_159, a1_o1_159] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_160, a1_o1_160]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_161 : IntRange, a1_o1_161 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_161, a1_o1_161]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_162 : IntRange, a1_o1_162 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_162, a1_o1_162]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_42 : IntRange, a2_o1_42 : CC, a1_v1_163 : IntRange, a1_o1_163 : AutoSoftCar, a1_v1_164 : IntRange, a1_o1_164 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_42, a2_o1_42, a1_v1_163, a1_o1_163] and AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1_164, a1_o1_164]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_165 : IntRange, a1_o1_165 : FCA, a1_v1_166 : IntRange, a1_o1_166 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_165, a1_o1_165] and AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_166, a1_o1_166]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_167 : IntRange, a1_o1_167 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_167, a1_o1_167]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_168 : IntRange, a1_o1_168 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_168, a1_o1_168]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_169 : IntRange, a1_o1_169 : FCA, a1_v1_170 : IntRange, a1_o1_170 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_169, a1_o1_169] and AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_170, a1_o1_170]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_171 : IntRange, a1_o1_171 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_171, a1_o1_171]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_172 : IntRange, a1_o1_172 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_172, a1_o1_172]
}
assert AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_43 : IntRange, a2_o1_43 : CC, a1_v1_173 : IntRange, a1_o1_173 : AutoSoftCar, a1_v1_174 : IntRange, a1_o1_174 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_43, a2_o1_43, a1_v1_173, a1_o1_173] and AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1_174, a1_o1_174]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_175 : IntRange, a1_o1_175 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_175, a1_o1_175]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_176 : IntRange, a1_o1_176 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_176, a1_o1_176]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_44 : IntRange, a2_o1_44 : CC, a1_v1_177 : IntRange, a1_o1_177 : AutoSoftCar, a1_v1_178 : IntRange, a1_o1_178 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_44, a2_o1_44, a1_v1_177, a1_o1_177] and AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1_178, a1_o1_178]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_179 : IntRange, a1_o1_179 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_179, a1_o1_179] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_45 : IntRange, a2_o1_45 : CC, a1_v1_180 : IntRange, a1_o1_180 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_45, a2_o1_45, a1_v1_180, a1_o1_180] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_181 : IntRange, a1_o1_181 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_181, a1_o1_181] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_46 : IntRange, a2_o1_46 : CC, a1_v1_182 : IntRange, a1_o1_182 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_46, a2_o1_46, a1_v1_182, a1_o1_182] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_183 : IntRange, a1_o1_183 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_183, a1_o1_183]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1_184 : IntRange, a1_o1_184 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_184, a1_o1_184]
}
assert AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1_47 : IntRange, a2_o1_47 : CC, a1_v1_185 : IntRange, a1_o1_185 : AutoSoftCar, a1_v1_186 : IntRange, a1_o1_186 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1_47, a2_o1_47, a1_v1_185, a1_o1_185] and AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1_186, a1_o1_186]
}
assert WSC_AutoSoft_BDS_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_t1 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_t2 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_acceleration_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1 : IntRange, a1_o1 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_acceleration_t3 [wsPre, wsPost, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_deceleration_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1 : IntRange, a1_o1 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_deceleration_t4 [wsPre, wsPost, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_steering_t5 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_steering_t5 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_t1 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_t2 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1 : IntRange, a2_o1 : CC, a1_v1 : IntRange, a1_o1 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t3 [wsPre, wsPost, a2_v1, a2_o1, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t4 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_t5 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1 : IntRange, a2_o1 : CC, a1_v1 : IntRange, a1_o1 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 [wsPre, wsPost, a2_v1, a2_o1, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1 : IntRange, a1_o1 : CC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 [wsPre, wsPost, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1 : IntRange, a1_o1 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 [wsPre, wsPost, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1 : IntRange, a2_o1 : CC, a1_v1 : IntRange, a1_o1 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 [wsPre, wsPost, a2_v1, a2_o1, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1 : IntRange, a1_o1 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 [wsPre, wsPost, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1 : IntRange, a1_o1 : HC |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 [wsPre, wsPost, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1 : IntRange, a1_o1 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_t1 [wsPre, wsPost, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a1_v1 : IntRange, a1_o1 : FCA |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 [wsPre, wsPost, a1_v1, a1_o1]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 {
    distinct_valid_WSs implies
    all wsPre : WS |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 [wsPre, wsPost]
}
assert WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 {
    distinct_valid_WSs implies
    all wsPre : WS |
    all a2_v1 : IntRange, a2_o1 : CC, a1_v1 : IntRange, a1_o1 : AutoSoftCar |
    some wsPost : {ws : WS - wsPre | WSTC [wsPre, ws]} |
    AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 [wsPre, wsPost, a2_v1, a2_o1, a1_v1, a1_o1]
}


check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_steering_t5 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_t1 for i
/*check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_t2 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_steering_t5 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_t1 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_t2 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_t1 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_t2 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
check WSC_AutoSoft_BDS_main_t1 for i
check WSC_AutoSoft_BDS_main_t2 for i
check WSC_AutoSoft_BDS_main_on_acceleration_t3 for i
check WSC_AutoSoft_BDS_main_on_deceleration_t4 for i
check WSC_AutoSoft_BDS_main_on_steering_t5 for i
check WSC_AutoSoft_BDS_main_on_CC_main_t1 for i
check WSC_AutoSoft_BDS_main_on_CC_main_t2 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for i
check WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for i
check WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for i
check WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for i
check WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for i
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for i
*/
/*
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_steering_t5 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_acceleration_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_steering_t5 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_deceleration_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_steering_t5_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t4_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_t5_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_t1_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4_AND_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_acceleration_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_deceleration_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_steering_t5 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_t5 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t6 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t7 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t8 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_engaged_main_t9 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_HP_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_active_alert_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_FCA_main_active_setFCALevel_t4 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t1 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t2 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
check WSC_AutoSoft_BDS_main_on_CC_main_enabled_main_SLC_main_t3 for exactly 1 RoadSegment, exactly 1 Driver, exactly 1 MapObject, exactly 1 RoadObject, exactly 1 Lane, exactly 1 AutoSoftCar, exactly 1 Drives, exactly 1 IsOn, exactly 1 AutoSoft, exactly 1 BDS, exactly 1 CC, exactly 1 HC, exactly 1 HP, exactly 1 FCA, exactly 1 SLC, exactly 1 Coord, exactly 1 Shape, exactly 1 Angle, exactly 1 IgnitionState, exactly 1 SpeedLim, exactly 1 WS
*/

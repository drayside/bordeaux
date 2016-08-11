--This is a largish output file showing how the partial instances work and how they are used
--Note the 198 world states in teh scope

abstract sig  AutoSoftCar {}
abstract sig  Driver {}
abstract sig Drives {}
abstract sig AutoSoft {}
abstract sig BDS {}
abstract sig CC {}
abstract sig Num {}
abstract sig Bool {}
abstract sig IgnitionState {}



one sig A1//,A2,A3//,A4
extends  AutoSoftCar{}
one sig I1,I2//,I3,I4
extends  IgnitionState{}
one sig AS1//,I2,I3,I4
extends  AutoSoft{}
one sig Dr0
extends  Driver{}
one sig Ds0
extends  Drives{}
one sig BDS0
extends  BDS{}
one sig CC0
extends  CC{}
one sig B0,B1
extends  Bool{}
one sig N0,N1
extends  Num{}



//Enums and partial instances don't seem to like each other
--enum Bool {true, false}
--enum IgnitionState {on, off}

--uniq 
sig WS {
    AutoSoftCars : set AutoSoftCar,
 /*   Drivers : set Driver,
    Drivess : set Drives,
    AutoSofts : set AutoSoft,
    BDSs : set BDS,
    CCs : set CC,*/
    AutoSoftCar_orientation : AutoSoftCars -> Num,
    AutoSoftCar_acceleration : AutoSoftCars -> Num,
    AutoSoftCar_speed : AutoSoftCars -> Num,
    AutoSoftCar_ignition : AutoSoftCars    ->   IgnitionState,
//,   
/* Driver_isAttentive : Drivers-> Bool,
    Drives_r1 : Drivess -> AutoSoftCars
,
    Drives_r2 : Drivess ->one Drivers,
    CC_computedAccel : CCs-> Num,
    CC_cruiseSpeed : CCs-> Num,
 	  AutoSoft_BDS : AutoSofts one->one BDSs,
    AutoSoft_CC : AutoSofts one->lone CCs*/
} {
    all o : AutoSoftCars | one o.AutoSoftCar_ignition
    all o : AutoSoftCars | one o.AutoSoftCar_speed
    all o : AutoSoftCars | one o.AutoSoftCar_acceleration 
    all o : AutoSoftCars | one o.AutoSoftCar_orientation
/*    all o : Drivers | one o.Driver_isAttentive
    all o : CCs | one o.CC_cruiseSpeed
    all o : CCs | one o.CC_computedAccel
	all driver : Drivers | one ((Drives_r2.driver)).Drives_r1 
	all autosoftcar : AutoSoftCars | one ((Drives_r1.autosoftcar)).Drives_r2*/
}

fact{
  //  all o : WS.AutoSoftCars | # (o.(WS.AutoSoftCar_ignition)) = 1

}

fact uniqueWS{
	all disj ws1,ws2:WS| 
ws1.AutoSoftCars != ws2.AutoSoftCars
or
ws1.AutoSoftCar_ignition != ws2.AutoSoftCar_ignition
or
/*ws1.Drivers != ws2.Drivers
or
ws1.Driver_isAttentive != ws2.Driver_isAttentive
or
ws1.Drivess != ws2.Drivess
or
ws1.Drives_r1!=ws2.Drives_r1
or*/
ws1.AutoSoftCar_orientation != ws2.AutoSoftCar_orientation
or
ws1.AutoSoftCar_acceleration != ws2.AutoSoftCar_acceleration
or
ws1.AutoSoftCar_speed != ws2.AutoSoftCar_speed
/*
or
ws1.AutoSofts != ws2.AutoSofts
or
ws1.BDSs != ws2.BDSs
or
ws1.CCs != ws2.CCs
or
ws1.Drives_r2 != ws2.Drives_r2
or
ws1.CC_computedAccel != ws2.CC_computedAccel
or
ws1.CC_cruiseSpeed != ws2.CC_cruiseSpeed
or
ws1.AutoSoft_BDS != ws2.AutoSoft_BDS
or
ws1.AutoSoft_CC != ws2.AutoSoft_CC
*/

}

/*
pred WSTC (wsPre, ws : WS) {
    wsPre.AutoSoft_BDS = ws.AutoSoft_BDS
    wsPre.AutoSoft_CC = ws.AutoSoft_CC
	all o : wsPre.Drivess & ws.Drivess | o.(wsPre.Drives_r1) = o.(ws.Drives_r1) and o.(wsPre.Drives_r2) = o.(ws.Drives_r2)	
}

pred distinct_valid_WSs {
  all ws,ws' : WS | ws = ws' iff (     
	ws.AutoSoftCars = ws'.AutoSoftCars and 
	ws.Drivers = ws'.Drivers and
	ws.Drivess = ws'.Drivess and
	ws.AutoSofts = ws'.AutoSofts and 
    ws.BDSs = ws'.BDSs and 
    ws.CCs = ws'.CCs and 
	ws.AutoSoftCar_orientation = ws'.AutoSoftCar_orientation and 
	ws.AutoSoftCar_ignition = ws'.AutoSoftCar_ignition and
	ws.AutoSoftCar_speed = ws'.AutoSoftCar_speed and 
	ws.AutoSoftCar_acceleration = ws'.AutoSoftCar_acceleration and 
	ws.Driver_isAttentive = ws'.Driver_isAttentive and 
    ws.Drives_r1 = ws'.Drives_r1 and
    ws.Drives_r2 = ws'.Drives_r2 and 
	ws.CC_computedAccel = ws'.CC_computedAccel and 
	ws.CC_cruiseSpeed = ws'.CC_cruiseSpeed and 
	ws.AutoSoft_BDS = ws'.AutoSoft_BDS and
	ws.AutoSoft_CC = ws'.AutoSoft_CC
  )
}
*/
//This is a partial instance for 2 world states lets say:


run {} for exactly 17 WS


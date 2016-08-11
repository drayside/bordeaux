--This is a largish output file showing how the partial instances work and how they are used
--Note the 198 world states in teh scope

sig AutoSoftCar {}
sig Driver {}
sig Drives {}
sig AutoSoft {}
sig BDS {}
sig CC {}
sig Num {}
sig Bool {}
sig IgnitionState {}

//Enums and partial instances don't seem to like each other
--enum Bool {true, false}
--enum IgnitionState {on, off}

uniq 
sig WS {
    AutoSoftCars : set AutoSoftCar,

    Drivers : set Driver,
/*    Drivess : set Drives,
    AutoSofts : set AutoSoft,
    BDSs : set BDS,
    CCs : set CC,
    */AutoSoftCar_orientation : AutoSoftCars -> Num,
//    AutoSoftCar_acceleration : AutoSoftCars -> Num,
//    AutoSoftCar_speed : AutoSoftCars -> Num,
   AutoSoftCar_ignition : AutoSoftCars   ->    IgnitionState,

  Driver_isAttentive : Drivers-> Bool/*,
 
   Drives_r1 : Drivess -> AutoSoftCars,

    Drives_r2 : Drivess ->one Drivers,
    CC_computedAccel : CCs-> Num,
    CC_cruiseSpeed : CCs-> Num,
 	  AutoSoft_BDS : AutoSofts one->one BDSs,
    AutoSoft_CC : AutoSofts one->lone CCs*/
} {
    all o : AutoSoftCars | one o.AutoSoftCar_ignition
//    all o : AutoSoftCars | one o.AutoSoftCar_speed
//    all o : AutoSoftCars | one o.AutoSoftCar_acceleration 
    all o : AutoSoftCars | one o.AutoSoftCar_orientation
 /*   all o : Drivers | one o.Driver_isAttentive
   all o : CCs | one o.CC_cruiseSpeed
    all o : CCs | one o.CC_computedAccel
	all driver : Drivers | one ((Drives_r2.driver)).Drives_r1 
	all autosoftcar : AutoSoftCars | one ((Drives_r1.autosoftcar)).Drives_r2*/
}

fact{
  //  all o : WS.AutoSoftCars | # (o.(WS.AutoSoftCar_ignition)) = 1

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
inst i {
AutoSoftCar = A1//+A2+A3//+A4  //AutoSoftCar0+AutoSoftCar1,
,Driver = Driver0,
Drives = Drives0,
AutoSoft = AutoSoft0,
BDS = BDS0,
CC = CC0,
Num = N0 + N1,
Bool = Bool0 + Bool1,
IgnitionState = I1 +I2 //+I3 +I4// + IgnitionState1
}

pred p[]{}
run p
//distinct_valid_WSs 
for i

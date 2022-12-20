module eMall
//open util/integer 
//open util/boolean 

//only CPMS used in the system are added

//-------SIG-----



sig CPO{
cpms: set CPMS}


sig EMSP{
	users: set User,
	charges: set Charge,
	cpos:set CPO
}

//approximated to int
sig CPMS{
	stations:set ChargingStation,
	maintainers:set Maintainer
//Maybe a bool 
}

abstract sig Person{
	//name: one Str,
	//surname: one Str,
 	//birthday: one Date,
//	mail: one Str,
 	//password: one Str,
} 
one sig User extends Person{
	vehicles: set Vehicle
}
one sig Maintainer extends Person{}

//batterylevel percentage of the battery, KWperKM to int easier
sig Vehicle{
	//batteryLevel: one Int,
	//KWperKm: one Int,
	location: one Location,
}{ 
//inRange[batteryLevel, 0, 100]
//inRange[KWperKm, 0, 100]
}

sig ChargingStation{
	position:one Location,
	//batteryPresent: one Bool,
	//batteryKWh: one Int,
	sockets: set ChargingSocket,
	strategy: one Strategy
} 
//{  batteryPresent.isTrue implies inRange[batteryKWh, 0, 100]}

sig ChargingSocket{
	chargingType: one ChargingType,
	//available: one Bool,
	//maximumPowerAmount: one Int,
	energySource:one EnergySource
}

//amount the number of Kw to charge the car (approximated from a float)
sig Charge{
	//paid: one Bool,
	station: one ChargingStation,
	user: one User
	//amount: one Int,
	//date: one Date
}

abstract sig Strategy{}
one sig Manual extends Strategy{}
one sig Automatic extends Strategy{}

abstract sig ChargingType{}
one sig SuperFast extends ChargingType{}
one sig Fast extends ChargingType{}
one sig Normal extends ChargingType{}

abstract sig EnergySource{}
one sig Battery extends EnergySource{
//capacity: one Int
}
one sig DSO extends EnergySource{}






//utils types

//simplified model, days from 01/01/1900
//sig Date{}

//sig Str{}

//simplified using int
sig Location{  
//	latitude: one Int,   
//	longitude: one Int
}{//  inRange[latitude, -90, 90] and   
//	inRange[longitude, -180, 180]
}

//-------FACTS------

//fact uniqueMailForUser{
//	no disjoint u1,u2: User | u1.mail = u2.mail}

fact uniqueLocationForStation{
	no disjoint s1,s2: ChargingStation | s1.position = s2.position}

fact uniqueCPOForCPMS{
	no disjoint c1,c2: CPO, cp:CPMS | cp in c1.cpms and cp in c2.cpms}

fact uniqueStationForCPMS{
	no disjoint c1,c2: CPMS, s:ChargingStation | s in c1.stations and s in c2.stations}

fact socketOnlyOneStation{
          all s:ChargingSocket| s in ChargingStation.sockets
	no disjoint c1,c2: ChargingStation, s:ChargingSocket|(s in c1.sockets and s in c2.sockets)}

fact noVehicleWithoutUser{
	all v:Vehicle|  v in User.vehicles}

fact noCPMSWithoutCPO{
	all c:CPMS|  c in CPO.cpms}

fact noStationWithoutCPMS{
	all s:ChargingStation|  s in CPMS.stations}

fact noUserWithoutEMSP{
	all u:User|  u in EMSP.users}

fact noChargeWithoutEMSP{
	all c:Charge|  c in EMSP.charges}

fact noChargeWithoutUserInTheEMSP{
	all c:Charge| c in EMSP.charges and c.user in EMSP.users
}

fact allChargeAreFromChargingStationInTheSystem{
	all s:Charge.station | s in EMSP.cpos.cpms.stations 
}
fact maintainersMantainStationOfTheSameCPO{
	all m:Maintainer, c1,c2:CPO|(not c1=c2 and m in c1.cpms.maintainers) implies m not in c2.cpms.maintainers 
}

//spiegare perche no cpms senza emsp non è un constraint 

//Predicates (major actions)



//the user creates a charge
pred UserCreatesACharge(e,e1:EMSP,u:User, s:ChargingStation){
one c:Charge  | u in e1.users and
c.user=u and c.station=s and  (not (e1 = e)) and  e1.users=e.users and
e1.cpos=e.cpos and e1.charges=e.charges+c
}
run UserCreatesACharge for 3 but exactly 2 EMSP

pred CPOSubscribeItselfToEMSP(e,e1:EMSP,cpo:CPO){
 not (e1 = e)
 e1.users=e.users
e1.cpos=e.cpos+cpo
}
run CPOSubscribeItselfToEMSP for 3 but exactly 2 EMSP, exactly 2 CPO

pred CPOAddCPMS(c,c1:CPO,cp:CPMS){
 not (c1 = c)
c.cpms=c1.cpms+cp
}
run CPOAddCPMS for 3 but exactly 2 CPO

pred CPOAddMantainerToCPMS(c:CPO,cp,cp1:CPMS,m:Maintainer){
 not (cp = cp1)
 cp1 in c.cpms
 cp in c.cpms
 cp.stations=cp1.stations
 cp.maintainers=cp1.maintainers+m
}
run CPOAddMantainerToCPMS for 3 but exactly 2 CPMS

pred CPOAddStationToCPMS(c:CPO,cp,cp1:CPMS,s:ChargingStation){
 not (cp = cp1)
 cp1 in c.cpms
 cp in c.cpms
 cp.maintainers = cp1.maintainers
 cp.stations=cp1.stations+s
}
run CPOAddStationToCPMS for 3 but exactly 2 CPO

pred CPOAddSocketToStation( s,s1:ChargingStation,sk:ChargingSocket){
 not (s = s1)
  s.position=s1.position
  s.strategy=s1.strategy
  s1.sockets=s.sockets+sk
}
//run CPOAddSocketToStation for 3 but exactly 2 ChargingStation
//does not work for limitation of the language, as a fact a socket can exist only in one station so the above pred does not found
//an instance, this is due of the Add patter (s=new station, s1=old station) as for now this pred is never runned but supposed as consistent

pred inRange[x: Int, min: Int, max: Int]{ 
	not min = none implies x>=min and    
	not max = none implies x<=max }

//Asserts

assert uniqueLocationForStationCheck{
 	no disjoint s1,s2: ChargingStation | s1.position = s2.position}
check uniqueLocationForStationCheck for 10

assert uniqueCPOForCPMSCheck{
	no disjoint c1,c2: CPO, cp:CPMS | cp in c1.cpms and cp in c2.cpms}
check uniqueCPOForCPMSCheck  for 10

assert uniqueStationForCPMSCheck{
	no disjoint c1,c2: CPMS, s:ChargingStation | s in c1.stations and s in c2.stations}
check uniqueStationForCPMSCheck for 10

assert socketOnlyOneStationCheck{
   all s:ChargingSocket| s in ChargingStation.sockets
	no disjoint c1,c2: ChargingStation, s:ChargingSocket|(s in c1.sockets and s in c2.sockets)}
check socketOnlyOneStationCheck for 10

assert noVehicleWithoutUserCheck{
	all v:Vehicle|  v in User.vehicles}
check noVehicleWithoutUserCheck for 10

assert noCPMSWithoutCPOCheck{
	all c:CPMS|  c in CPO.cpms}
check noCPMSWithoutCPOCheck for 10

assert noStationWithoutCPMSCheck{
	all s:ChargingStation|  s in CPMS.stations}
check noStationWithoutCPMSCheck for 10

assert noUserWithoutEMSP{
	all u:User|  u in EMSP.users}
check noUserWithoutEMSP for 10

assert noChargeWithoutEMSPCheck{
	all c:Charge|  c in EMSP.charges}
check noChargeWithoutEMSPCheck for 10

assert noChargeWithoutUserInTheEMSP{
	all c:Charge| c in EMSP.charges and c.user in EMSP.users}
check noChargeWithoutUserInTheEMSP for 10

assert allChargeAreFromChargingStationInTheSystemCheck{
	all s:Charge.station | s in EMSP.cpos.cpms.stations }
check allChargeAreFromChargingStationInTheSystemCheck for 10

assert maintainersMantainStationOfTheSameCPO{
	all m:Maintainer, c1,c2:CPO|(not c1=c2 and m in c1.cpms.maintainers) implies m not in c2.cpms.maintainers }
check maintainersMantainStationOfTheSameCPO for 10

pred show() {
#EMSP = 1
}
run show for 20

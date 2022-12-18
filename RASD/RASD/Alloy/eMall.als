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

fact oneEMSP{//we do not care about others
 	
}

fact socketOnlyOneStation{
	all c1,c2: ChargingStation, s:ChargingSocket | c1 != c2 implies not( s in c1.sockets and s in c2.sockets)}

fact noVehicleWithoutUser{
	all v:Vehicle|  v in User.vehicles}

fact noCPMSWithoutCPO{
	all c:CPMS|  c in CPO.cpms}

fact noStationWithoutCPMS{
	all s:ChargingStation|  s in CPMS.stations}

fact noSocketWithoutStation{
	all s:ChargingSocket|  s in ChargingStation.sockets}

fact noChargeWithoutEMSP{
	all c:Charge|  c in EMSP.charges}

fact allChargeAreFromChargingStationInTheSystem{
	all s:Charge.station | s in EMSP.cpos.cpms.stations 
}

//spiegare perche no cpms senza emsp non è un constraint 


//Predicates (major actions)

pred BookACharge(e, e1 :EMSP,c:Charge){
	e1.cpos=e.cpos
	e1.users=e.users
//	one c:Charge|
//c.user=u and c.station=cs and
	e1.charges=e.charges +c
}
run BookACharge for 3 but exactly 2 EMSP

pred inRange[x: Int, min: Int, max: Int]{ 
	not min = none implies x>=min and    
	not max = none implies x<=max }

//Asserts

assert uniqueLocationForStationCheck{
 	no disjoint s1,s2: ChargingStation | s1.position = s2.position}
//check uniqueLocationForStationCheck for 50

assert uniqueCPOForCPMSCheck{
	no disjoint c1,c2: CPO, cp:CPMS | cp in c1.cpms and cp in c2.cpms}
//check uniqueCPOForCPMSCheck  for 10

assert uniqueStationForCPMSCheck{
	no disjoint c1,c2: CPMS, s:ChargingStation | s in c1.stations and s in c2.stations}
//check uniqueStationForCPMSCheck for 10

assert socketOnlyOneStationCheck{
	all c1,c2: ChargingStation, s:ChargingSocket | c1 != c2 implies not( s in c1.sockets and s in c2.sockets)}
//check socketOnlyOneStationCheck for 10

assert noVehicleWithoutUserCheck{
	all v:Vehicle|  v in User.vehicles}
//check noVehicleWithoutUserCheck for 10

assert noCPMSWithoutCPOCheck{
	all c:CPMS|  c in CPO.cpms}
//check noCPMSWithoutCPOCheck for 10

assert noStationWithoutCPMSCheck{
	all s:ChargingStation|  s in CPMS.stations}
//check noStationWithoutCPMSCheck for 10

assert noSocketWithoutStationCheck{
	all s:ChargingSocket|  s in ChargingStation.sockets}
//check noSocketWithoutStationCheck for 10

assert noChargeWithoutEMSPCheck{
	all c:Charge|  c in EMSP.charges}
//check noChargeWithoutEMSPCheck for 10

assert allChargeAreFromChargingStationInTheSystemCheck{
	all s:Charge.station | s in EMSP.cpos.cpms.stations }
//check allChargeAreFromChargingStationInTheSystemCheck for 10

pred show() {
#EMSP = 1
#CPO=3
#Charge=4
}
run show for 7

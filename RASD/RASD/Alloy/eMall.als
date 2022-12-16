module eMall
//open util/integer 
//open util/boolean 

//-------SIG-----
abstract sig Role{}
one sig CPOMantainer extends Role{}
one sig DEFAULTUSER extends Role{}

sig User{
	//name: one Str,
	//surname: one Str,
 	//birthday: one Date,
	mail: one Str,
 	//password: one Str,
 	role: one Role,
	emsps: some EMSP
} 

//batterylevel percentage of the battery, KWperKM to int easier
sig Vehicle{
//batteryLevel: one Int,
location: one Location,
//KWperKm: one Int,
owner: some User
}{ 
//batteryLevel>=0 and batteryLevel<=100//inRange[batteryLevel, 0, 100]
//inRange[KWperKm, 0, 100]
 all o:owner | o.role= DEFAULTUSER}


sig CPO{
cpms: some CPMS}

//approximated to int
sig CPMS{
stations:some ChargingStation
}

abstract sig Strategy{}
one sig Manual extends Strategy{}
one sig Automatic extends Strategy{}

//amount the number of Kw to charge the car (approximated from a float)
sig Charge{
//paid: one Bool,
station: one ChargingStation,
user: one User
//amount: one Int,
//date: one Date
}

abstract sig ChargingType{}
one sig Rapid extends ChargingType{}
one sig Fast extends ChargingType{}
one sig Slow extends ChargingType{}

//TODO add energy source
sig EnergySource{}


sig ChargingSocket{
chargingStation: one ChargingStation,
chargingType: one ChargingType,
//available: one Bool,
//maximumPowerAmount: one Int,
energySource:one EnergySource}


sig ChargingStation{
position:one Location,
sockets: some ChargingSocket,
//batteryPresent: one Bool,
//batteryKWh: one Int,
strategy: one Strategy}
//{  batteryPresent.isTrue implies inRange[batteryKWh, 0, 100]}


abstract sig EMSP{
cpms: set CPMS,
}
//utils types

//simplified model, days from 01/01/1900
//sig Date{}

sig Str{}

//simplified using int
sig Location{  
	//latitude: one Int,   
	//longitude: one Int
}{  //inRange[latitude, -90, 90] and   
	//inRange[longitude, -180, 180]
}

//-------FACTS------

fact uniqueMailForUser{
	no disjoint u1,u2: User | u1.mail = u2.mail}

fact uniqueLocationForStation{
	no disjoint s1,s2: ChargingStation | s1.position = s2.position}

fact uniqueCPOForCPMS{
	no disjoint c1,c2: CPO | c1.cpms = c2.cpms}




pred inRange[x: Int, min: Int, max: Int]{ 
	not min = none implies x>=min and    
	not max = none implies x<=max }

pred show() {}
run show

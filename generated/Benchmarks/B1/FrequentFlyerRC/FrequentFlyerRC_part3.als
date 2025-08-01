abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}
one sig AddressD extends Address{}
one sig AddressE extends Address{}

abstract sig EstadoContrato{}
one sig SetFlyerAndReward extends EstadoContrato{}
one sig MilesAdded extends EstadoContrato{}

sig Miles {s: seq Int }

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig EstadoConcreto {
	_airlineRepresentative: Address,
	_flyer: Address,
	_rewardsPerMile: Int,
	_miles: Miles,
	_indexCalculatedUpto: Int,
	_totalRewards: Int,
	_state: lone EstadoContrato,
	_init: Bool
}


pred invariante[e:EstadoConcreto] {
	e._init = True
	e._state = SetFlyerAndReward implies (e._airlineRepresentative != Address0x0)
}

pred pre_constructor[ein: EstadoConcreto] {
	ein._init = False
	ein._airlineRepresentative = Address0x0
	ein._flyer = Address0x0
	ein._rewardsPerMile = 0
	ein._indexCalculatedUpto = 0
	ein._totalRewards = 0
	no ein._state
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address, flyer: Address, rewardsPerMile: Int] {

}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
				flyer: Address, rewardsPerMile: Int] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, flyer, rewardsPerMile]
	
	//Post
	eout._airlineRepresentative = sender
	eout._flyer = flyer
	eout._rewardsPerMile = rewardsPerMile
	eout._indexCalculatedUpto = 0
	eout._totalRewards = 0
	eout._state = SetFlyerAndReward
	eout._init = True

	#eout._miles.s = 0

	//eout._airlineRepresentative = ein._airlineRepresentative
	//eout._flyer = ein._flyer
	//eout._rewardsPerMile = ein._rewardsPerMile
	//eout._miles = ein._miles
	//eout._indexCalculatedUpto = ein._indexCalculatedUpto
	//eout._totalRewards = ein._totalRewards
	//eout._state = ein._state
}

pred pre_addMiles[ein: EstadoConcreto] {
	some ein._state
	ein._init = True
	ein._init = True
}

pred pre_params_addMiles[ein: EstadoConcreto, sender: Address, miles: Miles] {
	ein._flyer = sender
}

pred met_addMiles[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, miles: Miles] {
	//Pre
	pre_addMiles[ein]
	pre_params_addMiles[ein, sender, Miles]
	
	//Post
	agregarMiles[ein, eout, miles]
	//computeTotalRewards(ein,eout)
	eout._state = MilesAdded
	eout._init = ein._init

	//eout._airlineRepresentative = ein._airlineRepresentative
	//eout._flyer = ein._flyer
	//eout._rewardsPerMile = ein._rewardsPerMile
	//eout._miles = ein._miles
	//eout._indexCalculatedUpto = ein._indexCalculatedUpto
	//eout._totalRewards = ein._totalRewards
	//eout._state = ein._state
}

pred agregarMiles[ein: EstadoConcreto, eout: EstadoConcreto, miles: Miles] {
	#eout._miles.s = (#ein._miles.s).add[#miles.s]
	all x: Int | x>= 0 and x <= #ein._miles.s implies ein._miles.s[x] in eout._miles.s.elems
	all x: Int | x>= 0 and x <= #miles.s implies miles.s[x] in eout._miles.s.elems
}

pred pre_getMiles[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
}

pred pre_params_getMiles[ein: EstadoConcreto, sender: Address] {
}

pred getMiles[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_getMiles[ein]
	pre_params_getMiles[ein, sender]
	
	//Post
	eout = ein
}


// I add a predicate for each possible theoretical partition
pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = SetFlyerAndReward
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = MilesAdded
}

pred partitionINV[e: EstadoConcreto]{ // 
	not (invariante[e])
}

// add a predicate for each possible transition
/*
From S0 to S1 with action
*/



pred transition__S02__a__S01__mediante_met_addMiles{
	(some x,y:EstadoConcreto, v10:Address, v20:Miles |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_addMiles[x, y, v10, v20])
}

pred transition__S02__a__S02__mediante_met_addMiles{
	(some x,y:EstadoConcreto, v10:Address, v20:Miles |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_addMiles[x, y, v10, v20])
}

run transition__S02__a__S01__mediante_met_addMiles for 10 EstadoConcreto, 3 Miles
run transition__S02__a__S02__mediante_met_addMiles for 10 EstadoConcreto, 3 Miles

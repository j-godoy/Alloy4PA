abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}
one sig AddressD extends Address{}
one sig AddressE extends Address{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig EstadoContrato{}
one sig Created extends EstadoContrato{}
one sig InTransit extends EstadoContrato{}
one sig Completed extends EstadoContrato{}

abstract sig EstadoConcreto {
	_initiatingCounterparty: one Address,
	_counterparty: one Address,
	_previousCounterparty: one Address,
	_supplyChainOwner: one Address,
	_supplyChainObserver: one Address,
	_state: lone EstadoContrato,
	_init: Bool
}


pred invariante[e:EstadoConcreto] {
	e._init = True
	e._state = Created => e._counterparty = e._initiatingCounterparty
}

pred pre_constructor[ein: EstadoConcreto] {
	ein._init = False
	no ein._state
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address, supplyChainOwner:Address, supplyChainObserver:Address] {
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, supplyChainOwner:Address, supplyChainObserver:Address] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, supplyChainOwner, supplyChainObserver]

	eout._initiatingCounterparty = sender
	eout._init = True
	eout._previousCounterparty = Address0x0

	eout._counterparty = eout._initiatingCounterparty
	// eout._previousCounterparty = ein._previousCounterparty
	eout._supplyChainOwner = supplyChainOwner
	eout._supplyChainObserver = supplyChainObserver
	eout._state = Created	
}

pred pre_transferResponsibility[ein: EstadoConcreto] {
	some ein._state
	ein._init = True
	ein._state != Completed
}

pred pre_params_transferResponsibility[ein: EstadoConcreto, sender: Address, newCounterparty: Address]{
	ein._counterparty = sender
}

pred met_transferResponsibility[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, newCounterparty: Address]{
	//Pre
	pre_transferResponsibility[ein]
	pre_params_transferResponsibility[ein, sender, newCounterparty]
	
	//ein._state = Created or ein._state = InTransit
	//Post
	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = newCounterparty
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
    ein._state = Created => eout._state = InTransit else eout._state = ein._state
	eout._init = ein._init
}

pred pre_complete[ein: EstadoConcreto] {
	ein._init = True
	ein._state != Completed
	ein._state != Created
}

pred pre_params_complete[ein: EstadoConcreto, sender: Address]{
	ein._supplyChainOwner = sender
}

pred met_complete[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address]{
	//Pre
	pre_complete[ein]
	pre_params_complete[ein, sender]
	//Post
	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = Address0x0
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
	eout._state = Completed
	eout._init = ein._init
}


// I add a predicate for each possible theoretical partition
pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Created
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = InTransit
}

pred partitionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Completed
}

// add a predicate for each possible transition
/*
From S0 to S1 with action
*/



pred transition__S03__a__S01__mediante_met_transferResponsibility{
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_transferResponsibility[x, y, v10, v11])
}

pred transition__S03__a__S02__mediante_met_transferResponsibility{
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_transferResponsibility[x, y, v10, v11])
}

pred transition__S03__a__S03__mediante_met_transferResponsibility{
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_transferResponsibility[x, y, v10, v11])
}

run transition__S03__a__S01__mediante_met_transferResponsibility for 10 EstadoConcreto
run transition__S03__a__S02__mediante_met_transferResponsibility for 10 EstadoConcreto
run transition__S03__a__S03__mediante_met_transferResponsibility for 10 EstadoConcreto
pred transition__S03__a__S01__mediante_met_complete{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_complete[x, y, v10])
}

pred transition__S03__a__S02__mediante_met_complete{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_complete[x, y, v10])
}

pred transition__S03__a__S03__mediante_met_complete{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_complete[x, y, v10])
}

run transition__S03__a__S01__mediante_met_complete for 10 EstadoConcreto
run transition__S03__a__S02__mediante_met_complete for 10 EstadoConcreto
run transition__S03__a__S03__mediante_met_complete for 10 EstadoConcreto

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



//======predicates for blue queries======



pred blue_transition__S01__a__S02__mediante_met_transferResponsibility {
	some x: EstadoConcreto | partitionS01[x] and (not pre_transferResponsibility[x] or (all sender:{this/Address}, newCounterparty:{this/Address} | pre_params_transferResponsibility[x,sender, newCounterparty] implies some y:EstadoConcreto | met_transferResponsibility[x,y,sender, newCounterparty] and not partitionS02[y]))
}
run blue_transition__S01__a__S02__mediante_met_transferResponsibility for 10 EstadoConcreto

pred blue_transition__S02__a__S03__mediante_met_complete {
	some x: EstadoConcreto | partitionS02[x] and (not pre_complete[x] or (all sender:{this/Address} | pre_params_complete[x,sender] implies some y:EstadoConcreto | met_complete[x,y,sender] and not partitionS03[y]))
}
run blue_transition__S02__a__S03__mediante_met_complete for 10 EstadoConcreto

pred blue_transition__S00__a__S01__mediante_met_constructor {
	some x: EstadoConcreto | partitionS00[x] and ((all sender:{this/Address}, supplyChainOwner:{this/Address}, supplyChainObserver:{this/Address} | pre_params_constructor[x,sender, supplyChainOwner, supplyChainObserver] implies some y:EstadoConcreto | met_constructor[x,y,sender, supplyChainOwner, supplyChainObserver] and not partitionS01[y]))
}
run blue_transition__S00__a__S01__mediante_met_constructor for 10 EstadoConcreto

pred blue_transition__S02__a__S02__mediante_met_transferResponsibility {
	some x: EstadoConcreto | partitionS02[x] and (not pre_transferResponsibility[x] or (all sender:{this/Address}, newCounterparty:{this/Address} | pre_params_transferResponsibility[x,sender, newCounterparty] implies some y:EstadoConcreto | met_transferResponsibility[x,y,sender, newCounterparty] and not partitionS02[y]))
}
run blue_transition__S02__a__S02__mediante_met_transferResponsibility for 10 EstadoConcreto




//======predicates for turquoise queries======




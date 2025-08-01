// concrete states
abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}
one sig AddressD extends Address{}
one sig AddressE extends Address{}

abstract sig EstadoContrato{}
one sig Create extends EstadoContrato{}
one sig ComputeTotal extends EstadoContrato{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

one sig Secuencia{s1:seq Int} {s1[0]=1 and s1[1]=2 and s1[2]=3 and #s1=3}

abstract sig EstadoConcreto {
	_manufacturer: Address,
	_defectiveComponentsCount: Secuencia,
	_total: Int,
	_state: EstadoContrato,
	_init: Bool
}

pred invariante[e:EstadoConcreto] {
	e._init = True
	e._manufacturer != Address0x0
	e._total = allsum[e._defectiveComponentsCount.s1.elems]
}

pred pre_constructor[ein: EstadoConcreto] {
	ein._init = False
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address, defectiveComponentsCount: Secuencia] {
	sender != Address0x0
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, defectiveComponentsCount: Secuencia] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, defectiveComponentsCount]

	//Post
	eout._manufacturer = sender
	eout._defectiveComponentsCount = defectiveComponentsCount
	// eout._total = 0
	eout._total = allsum[ein._defectiveComponentsCount.s1.elems]
	eout._state = Create
	eout._init = True

	//eout._manufacturer = ein._manufacturer
	//eout._defectiveComponentsCount = ein._defectiveComponentsCount
	//eout._total = ein._total
	//eout._state = ein._state
}

pred pre_computeTotal[ein: EstadoConcreto] {
	some ein._state
	ein._state != ComputeTotal
	ein._init = True
}

pred pre_params_computeTotal[ein: EstadoConcreto, sender: Address] {
	ein._manufacturer = sender
}

pred met_computeTotal[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_computeTotal[ein]
	pre_params_computeTotal[ein, sender]
	
	//Post
	// calculate total for only the first 12 values, in case more than 12 are entered
	eout._total = allsum[ein._defectiveComponentsCount.s1.elems]
	eout._state = ComputeTotal
	
	eout._manufacturer = ein._manufacturer
	eout._defectiveComponentsCount = ein._defectiveComponentsCount
	eout._init = ein._init
	//eout._total = ein._total
	//eout._state = ein._state
}

// Tiene el problema de que no suma repetidos.
fun allsum[defectiveComponentsCount: set Int] : Int {
    sum s: defectiveComponentsCount | s
}

pred pre_getDefectiveComponentsCount[ein: EstadoConcreto] {
	ein._init = True
}

pred pre_params_getDefectiveComponentsCount[ein: EstadoConcreto, sender: Address] {
}

pred met_getDefectiveComponentsCount[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	//Post
	eout = ein
}




// I add a predicate for each possible theoretical partition
pred partitionS00[e: EstadoConcreto]{ // 
	// invariante[e]
	pre_constructor[e]
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Create
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = ComputeTotal
}

pred partitionINV[e: EstadoConcreto]{ // 
	not (invariante[e])
}


// add a predicate for each possible transition
/*
From S0 to S1 with action
*/



//======predicates for blue queries======



pred blue_transition__S00__a__S01__mediante_met_constructor {
	some x: EstadoConcreto | partitionS00[x] and ((all sender:{this/Address}, defectiveComponentsCount:{this/Secuencia} | pre_params_constructor[x,sender, defectiveComponentsCount] implies some y:EstadoConcreto | met_constructor[x,y,sender, defectiveComponentsCount] and not partitionS01[y]))
}
run blue_transition__S00__a__S01__mediante_met_constructor for 10 EstadoConcreto, 4 Int

pred blue_transition__S01__a__S02__mediante_met_computeTotal {
	some x: EstadoConcreto | partitionS01[x] and (not pre_computeTotal[x] or (all sender:{this/Address} | pre_params_computeTotal[x,sender] implies some y:EstadoConcreto | met_computeTotal[x,y,sender] and not partitionS02[y]))
}
run blue_transition__S01__a__S02__mediante_met_computeTotal for 10 EstadoConcreto, 4 Int

pred blue_transition__S01__a__S01__mediante_met_getDefectiveComponentsCount {
	some x: EstadoConcreto | partitionS01[x] and (not pre_getDefectiveComponentsCount[x] or (all sender:{this/Address} | pre_params_getDefectiveComponentsCount[x,sender] implies some y:EstadoConcreto | met_getDefectiveComponentsCount[x,y,sender] and not partitionS01[y]))
}
run blue_transition__S01__a__S01__mediante_met_getDefectiveComponentsCount for 10 EstadoConcreto, 4 Int

pred blue_transition__S02__a__S02__mediante_met_getDefectiveComponentsCount {
	some x: EstadoConcreto | partitionS02[x] and (not pre_getDefectiveComponentsCount[x] or (all sender:{this/Address} | pre_params_getDefectiveComponentsCount[x,sender] implies some y:EstadoConcreto | met_getDefectiveComponentsCount[x,y,sender] and not partitionS02[y]))
}
run blue_transition__S02__a__S02__mediante_met_getDefectiveComponentsCount for 10 EstadoConcreto, 4 Int




//======predicates for turquoise queries======




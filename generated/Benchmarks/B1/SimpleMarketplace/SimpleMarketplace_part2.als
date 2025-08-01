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

abstract sig Texto{}
one sig TextoA extends Texto{}
one sig TextoB extends Texto{}
one sig TextoC extends Texto{}
one sig TextoD extends Texto{}

abstract sig EstadoContrato{}
one sig ItemAvailable extends EstadoContrato{}
one sig OfferPlaced extends EstadoContrato{}
one sig Accepted extends EstadoContrato{}

abstract sig EstadoConcreto {
	_instanceOwner: Address,
	_instanceBuyer: Address,
	_description: lone Texto,
	_askingPrice: Int,
	_offerPrice: Int,
	_state: lone EstadoContrato,
	_init: Bool
}


pred invariante[e:EstadoConcreto] {
	e._init = True
	e._offerPrice >= 0
	e._askingPrice >= 0
}

pred pre_constructor[ein: EstadoConcreto] {
	no ein._state
	ein._init = False
	ein._instanceBuyer = Address0x0
	no ein._description
	ein._askingPrice = 0
	ein._instanceOwner = Address0x0
	ein._offerPrice = 0
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address, description: Texto, price: Int] {
	price >= 0 // Esto lo agregué pero no está en el código
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, description: Texto, price: Int] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, description, price]

	//Post
	eout._instanceOwner = sender
	eout._description = description
	eout._askingPrice = price
	eout._state = ItemAvailable
	eout._init = True

	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
}

pred pre_makeOffer[ein: EstadoConcreto] {
	some ein._state
	ein._state = ItemAvailable
}

pred pre_params_makeOffer[ein: EstadoConcreto, sender:Address, offerPrice: Int] {
	offerPrice > 0
	ein._instanceOwner != sender
}

pred met_makeOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, offerPrice: Int] {
	//Pre
	pre_makeOffer[ein]
	pre_params_makeOffer[ein, sender, offerPrice]
	
	//Post
	eout._instanceOwner = ein._instanceOwner
	eout._instanceBuyer = sender
	eout._description = ein._description
	eout._askingPrice = ein._askingPrice
	eout._offerPrice = offerPrice
	eout._state = OfferPlaced
	eout._init = ein._init
}

pred pre_reject[ein: EstadoConcreto] {
	some ein._state
	ein._state = OfferPlaced
}

pred pre_params_reject[ein: EstadoConcreto, sender:Address] {
	ein._instanceOwner = sender
}

pred met_reject[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_reject[ein]
	pre_params_reject[ein, sender]

	//Post
	eout._instanceOwner = ein._instanceOwner
	eout._instanceBuyer = Address0x0

	eout._description = ein._description
	eout._askingPrice = ein._askingPrice
	eout._offerPrice = ein._offerPrice
	eout._state = ItemAvailable
	eout._init = ein._init
}

pred pre_acceptOffer[ein: EstadoConcreto] {
	some ein._state
	ein._state != ItemAvailable
	ein._state != Accepted // agrego FIX
}

pred pre_params_acceptOffer[ein: EstadoConcreto, sender:Address] {
	ein._instanceOwner = sender
}

pred met_acceptOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_acceptOffer[ein]
	pre_params_acceptOffer[ein, sender]

	//Post
	eout._instanceOwner = ein._instanceOwner
	eout._instanceBuyer = ein._instanceBuyer
	eout._description = ein._description
	eout._askingPrice = ein._askingPrice
	eout._offerPrice = ein._offerPrice
	eout._state = Accepted
	eout._init = ein._init
}


// I add a predicate for each possible theoretical partition
pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = ItemAvailable
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = OfferPlaced
}

pred partitionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Accepted
}

pred partitionINV[e: EstadoConcreto]{ // 
	not (invariante[e])
}


// add a predicate for each possible transition
/*
From S0 to S1 with action
*/



pred transition__S01__a__S01__mediante_met_makeOffer{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_makeOffer[x, y, v10, v20])
}

pred transition__S01__a__S02__mediante_met_makeOffer{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_makeOffer[x, y, v10, v20])
}

pred transition__S01__a__S03__mediante_met_makeOffer{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_makeOffer[x, y, v10, v20])
}

run transition__S01__a__S01__mediante_met_makeOffer for 10 EstadoConcreto
run transition__S01__a__S02__mediante_met_makeOffer for 10 EstadoConcreto
run transition__S01__a__S03__mediante_met_makeOffer for 10 EstadoConcreto
pred transition__S01__a__S01__mediante_met_reject{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_reject[x, y, v10])
}

pred transition__S01__a__S02__mediante_met_reject{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_reject[x, y, v10])
}

pred transition__S01__a__S03__mediante_met_reject{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_reject[x, y, v10])
}

run transition__S01__a__S01__mediante_met_reject for 10 EstadoConcreto
run transition__S01__a__S02__mediante_met_reject for 10 EstadoConcreto
run transition__S01__a__S03__mediante_met_reject for 10 EstadoConcreto
pred transition__S01__a__S01__mediante_met_acceptOffer{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_acceptOffer[x, y, v10])
}

pred transition__S01__a__S02__mediante_met_acceptOffer{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_acceptOffer[x, y, v10])
}

pred transition__S01__a__S03__mediante_met_acceptOffer{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_acceptOffer[x, y, v10])
}

run transition__S01__a__S01__mediante_met_acceptOffer for 10 EstadoConcreto
run transition__S01__a__S02__mediante_met_acceptOffer for 10 EstadoConcreto
run transition__S01__a__S03__mediante_met_acceptOffer for 10 EstadoConcreto

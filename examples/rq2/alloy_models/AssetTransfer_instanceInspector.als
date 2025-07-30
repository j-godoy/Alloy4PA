// concrete states
abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}
one sig AddressD extends Address{}
one sig AddressE extends Address{}

abstract sig Texto{}
one sig TextoA extends Texto{}
one sig TextoB extends Texto{}
one sig TextoC extends Texto{}
one sig TextoD extends Texto{}

abstract sig EstadoContrato{}
one sig Active extends EstadoContrato{}
one sig OfferPlaced extends EstadoContrato{}
one sig PendingInspection extends EstadoContrato{}
one sig Inspected extends EstadoContrato{}
one sig Appraised extends EstadoContrato{}
one sig NotionalAcceptance extends EstadoContrato{}
one sig BuyerAccepted extends EstadoContrato{}
one sig SellerAccepted extends EstadoContrato{}
one sig Accepted extends EstadoContrato{}
one sig Terminated extends EstadoContrato{}


abstract sig EstadoConcreto {
	_instanceOwner: Address,
	_description: Texto,
	_askingPrice: Int,
	_instanceBuyer: Address,
	_offerPrice: Int,
	_instanceInspector: Address,
	_instanceAppraiser: Address,
	_state: EstadoContrato,
	_init: Bool
}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}


//fact {all x: Int | x > 0}

pred invariante[e:EstadoConcreto] {
	e._init = True
	e._instanceOwner != Address0x0
	e._instanceOwner != e._instanceBuyer
	e._offerPrice >= 0
	e._askingPrice >= 0
	e._instanceBuyer = Address0x0 implies (e._state = Active or e._state = Terminated)
	e._instanceInspector = Address0x0 implies (e._state = Active or e._state = Terminated)
	e._instanceAppraiser = Address0x0 implies (e._state = Active or e._state = Terminated)
}

pred pre_constructor[ein:EstadoConcreto] {
	ein._init = False
	ein._instanceBuyer = Address0x0
	ein._offerPrice = 0
	ein._instanceInspector = Address0x0
	ein._instanceAppraiser = Address0x0
}

pred pre_params_constructor[ein: EstadoConcreto, sender: Address, description: Texto, price: Int] {
	price >= 0
	sender != Address0x0
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, description: Texto, price: Int] {
	//Pre
	pre_constructor[ein]

	//Post
	eout._instanceOwner = sender
	eout._askingPrice = price
	eout._description = description
	eout._state = Active
	eout._init = True

	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
}

pred pre_terminate[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state != Terminated and ein._state != Accepted and ein._state != SellerAccepted// agrego FIX
}

pred pre_params_terminate[ein: EstadoConcreto, sender:Address] {
	sender != Address0x0
	ein._instanceOwner = sender
}

pred met_terminate[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_terminate[ein]
	pre_params_terminate[ein, sender]

	//Post
	eout._state = Terminated

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._init = ein._init
}

pred pre_modify[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = Active
}

pred pre_params_modify[ein: EstadoConcreto, sender: Address, description: Texto, price: Int] {
	sender != Address0x0
	ein._instanceOwner = sender
}

pred met_modify[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, description: Texto, price: Int] {
	//Pre
	pre_modify[ein]
	pre_params_modify[ein, sender, description, price]

	//Post
	eout._description = description
	eout._askingPrice = price

	eout._instanceOwner = ein._instanceOwner
	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._state = ein._state
	eout._init = ein._init
}

pred pre_makeOffer[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = Active
}

pred pre_params_makeOffer[ein: EstadoConcreto, sender: Address, inspector: Address, appraiser: Address, offerPrice: Int] {
	sender != Address0x0
	ein._instanceOwner != sender
	inspector != Address0x0 and appraiser != Address0x0 and offerPrice != 0
}

pred met_makeOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, inspector: Address,
		appraiser: Address, offerPrice: Int] {
	//Pre
	pre_makeOffer[ein]
	pre_params_makeOffer[ein, sender, inspector, appraiser, offerPrice]
	
	//Post
	eout._instanceBuyer = sender
	eout._instanceInspector = inspector
	eout._instanceAppraiser = appraiser
	eout._offerPrice = offerPrice
	eout._state = OfferPlaced
	
	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._init = ein._init
}

pred pre_acceptOffer[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = OfferPlaced
}

pred pre_params_acceptOffer[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
	ein._instanceOwner = sender
}

pred met_acceptOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_acceptOffer[ein]
	pre_params_acceptOffer[ein, sender]
	
	//Post
	eout._state = PendingInspection
	eout._instanceBuyer = ein._instanceBuyer
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._offerPrice = ein._offerPrice
	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._init = ein._init
}

pred pre_reject[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	(ein._state = OfferPlaced or ein._state = PendingInspection or ein._state = Inspected 
	   or ein._state = Appraised or ein._state = NotionalAcceptance or ein._state = BuyerAccepted)
}

pred pre_params_reject[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
	ein._instanceOwner = sender
}

pred met_reject[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_reject[ein]
	pre_params_reject[ein, sender]
	

	//Post
	eout._instanceBuyer = Address0x0
	eout._state = Active

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._init = ein._init
}

pred pre_accept[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = NotionalAcceptance or ein._state = BuyerAccepted or ein._state = SellerAccepted
}

pred pre_params_accept[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
	(ein._instanceOwner = sender or ein._instanceBuyer = sender)
	(sender != ein._instanceOwner or ein._state = NotionalAcceptance or ein._state = BuyerAccepted)
	(sender != ein._instanceBuyer or ein._state = NotionalAcceptance or ein._state = SellerAccepted)
}

pred met_accept[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_accept[ein]
	pre_params_accept[ein, sender]
	

	//Post
        (sender = ein._instanceBuyer) =>
		(
	         	(ein._state = NotionalAcceptance) => (eout._state = BuyerAccepted)
			else (
					(ein._state = SellerAccepted) => (eout._state = Accepted)
					else (eout._state = ein._state)
				)
		)
	else
		(
	         	(ein._state = NotionalAcceptance) => (eout._state = SellerAccepted)
			else (
					(ein._state = BuyerAccepted) => (eout._state = Accepted)
					else (eout._state = ein._state)
				)
		)

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._init = ein._init
}

pred pre_modifyOffer[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = OfferPlaced
}

pred pre_params_modifyOffer[ein: EstadoConcreto, sender: Address, offerPrice: Int] {
	sender != Address0x0
	ein._instanceBuyer = sender or offerPrice != 0 // BUGGY
	// ein._instanceBuyer = sender and offerPrice != 0 // FIX
}

pred met_modifyOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, offerPrice: Int] {
	//Pre
	pre_modifyOffer[ein]
	pre_params_modifyOffer[ein, sender, offerPrice]
	
	
	//Post
	eout._offerPrice = offerPrice

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceBuyer = ein._instanceBuyer
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._state = ein._state
	eout._init = ein._init
}

pred pre_rescindOffer[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	(ein._state = OfferPlaced or ein._state = PendingInspection or ein._state = Inspected
		or ein._state = Appraised or ein._state = NotionalAcceptance or ein._state = SellerAccepted)
}

pred pre_params_rescindOffer[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
	ein._instanceBuyer = sender
}

pred met_rescindOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_rescindOffer[ein]
	pre_params_rescindOffer[ein, sender]
	
	//Post
	eout._instanceBuyer = Address0x0
        eout._offerPrice = 0
        eout._state = Active

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._init = ein._init
}

pred pre_markAppraised[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = PendingInspection or ein._state = Inspected
}

pred pre_params_markAppraised[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
	ein._instanceAppraiser = sender
}

pred met_markAppraised[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_markAppraised[ein]
	pre_params_markAppraised[ein, sender]
	
	//Post
	(ein._state = PendingInspection) => (eout._state = Appraised)
	else
		(ein._state = Inspected) => (eout._state =  NotionalAcceptance)
		else (eout._state = ein._state)

	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._init = ein._init
}

pred pre_markInspected[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = PendingInspection or ein._state = Appraised
}

pred pre_params_markInspected[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
	ein._instanceInspector = sender
}

pred met_markInspected[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_markInspected[ein]
	pre_params_markInspected[ein, sender]
	
	//Post
	(ein._state = PendingInspection) => (eout._state = Inspected)
	else 
		(ein._state = Appraised) => (eout._state =  NotionalAcceptance)
		else (eout._state = ein._state)

	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._description = ein._description
	eout._instanceInspector = ein._instanceInspector
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._init = ein._init
}

// I add a predicate for each possible theoretical partition
pred partitionS00[e: EstadoConcreto]{ // 
	e._init = False
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Active
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = OfferPlaced
}

pred partitionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = PendingInspection
}

pred partitionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Inspected
}

pred partitionS05[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Appraised
}

pred partitionS06[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = NotionalAcceptance
}

pred partitionS07[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = SellerAccepted
}

pred partitionS08[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = BuyerAccepted
}

pred partitionS09[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Accepted
}

pred partitionS10[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Terminated 
}
pred partitionINV[e: EstadoConcreto]{ // 
	not (invariante[e])
}




// add a predicate for each possible transition
/*
From S0 to S1 with action
*/

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

abstract sig Message{}
one sig MessageA extends Message{}
one sig MessageB extends Message{}
one sig MessageC extends Message{}
one sig MessageD extends Message{}

abstract sig EstadoContrato{}
one sig Request extends EstadoContrato{}
one sig Respond extends EstadoContrato{}

abstract sig EstadoConcreto {
	_requestor: Address,
	_responder: Address,
	_requestMessage: lone Message,
	_responseMessage: lone Message,
	_state: lone EstadoContrato,
	_init: Bool
}


pred invariante[e:EstadoConcreto] {
	e._init = True
}

pred pre_constructor[ein: EstadoConcreto] {
	no ein._state
	ein._init = False
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address, message: Message] {

}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, message: Message] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, message]

	eout._init = True
	
	//Post
	eout._requestor = sender
	eout._responder = ein._responder
	eout._requestMessage = message
	eout._responseMessage = ein._responseMessage
	eout._state = Request
}

pred pre_sendRequest[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = Respond // agrego FIX
}

pred pre_params_sendRequest[ein: EstadoConcreto, sender:Address, requestMessage: Message] {
	ein._requestor = sender
}

pred met_sendRequest[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, requestMessage: Message] {
	//Pre
	pre_sendRequest[ein]
	pre_params_sendRequest[ein, sender, requestMessage]
	
	//Post
	eout._requestMessage = requestMessage
	eout._state = Request
	eout._requestor = ein._requestor
	eout._responder = ein._responder
	eout._responseMessage = ein._responseMessage
	eout._init = ein._init
}

pred pre_sendResponse[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = Request // agrego FIX
}

pred pre_params_sendResponse[ein: EstadoConcreto, sender:Address, responseMessage: Message] {

}

pred met_sendResponse[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, responseMessage: Message] {
	//Pre
	pre_sendResponse[ein]
	pre_params_sendResponse[ein, sender, responseMessage]

	//Post
	eout._responseMessage = responseMessage
	eout._state = Respond
	eout._requestor = ein._requestor
	eout._responder = ein._responder
	eout._requestMessage = ein._requestMessage
	eout._init = ein._init
}


// I add a predicate for each possible theoretical partition
pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Request
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Respond
}

pred partitionINV[e: EstadoConcreto]{ // 
	not (invariante[e])
}


// add a predicate for each possible transition
/*
From S0 to S1 with action
*/


//======predicates for blue queries======



pred blue_transition__S01__a__S02__mediante_met_sendResponse {
	some x: EstadoConcreto | partitionS01[x] and (not pre_sendResponse[x] or (all sender:{this/Address}, responseMessage:{this/Message} | pre_params_sendResponse[x,sender, responseMessage] implies some y:EstadoConcreto | met_sendResponse[x,y,sender, responseMessage] and not partitionS02[y]))
}
run blue_transition__S01__a__S02__mediante_met_sendResponse for 10 EstadoConcreto, 4 Message

pred blue_transition__S00__a__S01__mediante_met_constructor {
	some x: EstadoConcreto | partitionS00[x] and ((all sender:{this/Address}, message:{this/Message} | pre_params_constructor[x,sender, message] implies some y:EstadoConcreto | met_constructor[x,y,sender, message] and not partitionS01[y]))
}
run blue_transition__S00__a__S01__mediante_met_constructor for 10 EstadoConcreto, 4 Message

pred blue_transition__S02__a__S01__mediante_met_sendRequest {
	some x: EstadoConcreto | partitionS02[x] and (not pre_sendRequest[x] or (all sender:{this/Address}, requestMessage:{this/Message} | pre_params_sendRequest[x,sender, requestMessage] implies some y:EstadoConcreto | met_sendRequest[x,y,sender, requestMessage] and not partitionS01[y]))
}
run blue_transition__S02__a__S01__mediante_met_sendRequest for 10 EstadoConcreto, 4 Message




//======predicates for turquoise queries======




abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}
one sig AddressD extends Address{}

abstract sig Texto{}
one sig TextoPending extends Texto{}
one sig TextoRejected extends Texto{}
one sig TextoApproved extends Texto{}
one sig TextoShared extends Texto{}
one sig TextoAvailable extends Texto{}
one sig TextoVacio extends Texto{}
one sig TextoOtro extends Texto{}

abstract sig EstadoContrato{}
one sig Requested extends EstadoContrato{}
one sig DocumentReview extends EstadoContrato{}
one sig AvailableToShare extends EstadoContrato{}
one sig SharingRequestPending extends EstadoContrato{}
one sig SharingWithThirdParty extends EstadoContrato{}
one sig Terminated extends EstadoContrato{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig EstadoConcreto {
	_owner: Address,
	_bankAgent: Address,
	_lockerFriendlyName: Texto,
	_lockerIdentifier: lone Texto,
	_currentAuthorizedUser: Address,
	_expirationDate: lone Texto,
	_image: lone Texto,
	_thirdPartyRequestor: lone Address,
	_intendedPurpose: lone Texto,
	_lockerStatus: lone Texto,
	_rejectionReason: lone Texto,
	_state: EstadoContrato,
	_init: Bool
}


pred invariante[e:EstadoConcreto] {
	e._init = True
	// (e._state = SharingRequestPending or e._state = SharingWithThirdParty) implies e._currentAuthorizedUser != Address0x0
	e._state = SharingWithThirdParty implies e._currentAuthorizedUser = e._thirdPartyRequestor
}

pred pre_constructor[ein: EstadoConcreto] {
	ein._init = False
}

pred pre_params_constructor[ein: EstadoConcreto, sender: Address, bankAgent: Address, lockerFriendlyName: Texto] {
	sender != Address0x0
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, bankAgent: Address, lockerFriendlyName: Texto] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, bankAgent, lockerFriendlyName]
	
	//Post
	eout._owner = sender
	eout._lockerFriendlyName  = lockerFriendlyName
	eout._state = Requested //////////////// should be StateType.Requested?
	eout._bankAgent = bankAgent
	eout._init = True

	//eout._owner = ein._owner
	//eout._bankAgent = ein._bankAgent
	//eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
}

pred pre_beginReviewProcess[ein: EstadoConcreto] {
	some ein._state
	ein._state =  Requested// agrego FIX
	ein._init = True
}

pred pre_params_beginReviewProcess[ein: EstadoConcreto, sender: Address] {
	ein._owner != sender
}

pred met_beginReviewProcess[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_beginReviewProcess[ein]
	pre_params_beginReviewProcess[ein, sender]	
	
	//Post
	eout._bankAgent = sender
	eout._lockerStatus = TextoPending
	eout._state = DocumentReview

	eout._owner = ein._owner
	//eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
	eout._init = ein._init
}

// pred pre_rejectApplication[ein: EstadoConcreto] {
// 	some ein._state
// 	ein._init = True
// }

// pred pre_params_rejectApplication[ein: EstadoConcreto, sender: Address, rejectionReason: Texto] {
// 	ein._bankAgent = sender
// }

// pred ocultar_met_rejectApplication[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, rejectionReason: Texto] {
// 	//Pre
// 	pre_rejectApplication[ein]
// 	pre_params_rejectApplication[ein, sender, rejectionReason]
	
// 	//Post
// 	eout._rejectionReason = rejectionReason
// 	eout._lockerStatus = TextoRejected
// 	eout._state = DocumentReview

// 	eout._owner = ein._owner
// 	eout._bankAgent = ein._bankAgent
// 	eout._lockerFriendlyName = ein._lockerFriendlyName
// 	eout._lockerIdentifier = ein._lockerIdentifier
// 	eout._currentAuthorizedUser = ein._currentAuthorizedUser
// 	eout._expirationDate = ein._expirationDate
// 	eout._image = ein._image
// 	eout._thirdPartyRequestor = ein._thirdPartyRequestor
// 	eout._intendedPurpose = ein._intendedPurpose
// 	//eout._lockerStatus = ein._lockerStatus
// 	//eout._rejectionReason = ein._rejectionReason
// 	//eout._state = ein._state
// 	eout._init = ein._init
// }

pred pre_uploadDocuments[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state =  DocumentReview// agrego FIX
}

pred pre_params_uploadDocuments[ein: EstadoConcreto, sender:Address, lockerIdentifier: Texto, image: Texto] {
	ein._bankAgent = sender
}

pred met_uploadDocuments[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, lockerIdentifier: Texto, image: Texto] {
	//Pre
	pre_uploadDocuments[ein]
	pre_params_uploadDocuments[ein, sender, lockerIdentifier, image]
	
	//Post
	eout._lockerStatus = TextoApproved
	eout._image = image
	eout._lockerIdentifier = lockerIdentifier
	eout._state = AvailableToShare

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	//eout._lockerIdentifier = ein._lockerIdentifier
	eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	//eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
	eout._init = ein._init
}

pred pre_shareWithThirdParty[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state =  AvailableToShare// agrego FIX
}

pred pre_params_shareWithThirdParty[ein: EstadoConcreto, sender: Address,
				thirdPartyRequestor: Address, expirationDate: Texto, intendedPurpose: Texto] {
	ein._owner = sender
}	

pred met_shareWithThirdParty[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address,
				thirdPartyRequestor: Address, expirationDate: Texto, intendedPurpose: Texto] {
	//Pre
	pre_shareWithThirdParty[ein]
	pre_params_shareWithThirdParty[ein, sender, thirdPartyRequestor, expirationDate, intendedPurpose]
	
	
	//Post
	eout._thirdPartyRequestor = thirdPartyRequestor
	eout._currentAuthorizedUser = thirdPartyRequestor
	eout._lockerStatus = TextoShared
	eout._intendedPurpose = intendedPurpose
	eout._expirationDate = expirationDate
	eout._state = SharingWithThirdParty

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	//eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	//eout._thirdPartyRequestor = ein._thirdPartyRequestor
	//eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
	eout._init = ein._init
}

pred pre_acceptSharingRequest[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state =  SharingRequestPending// agrego FIX
}

pred pre_params_acceptSharingRequest[ein: EstadoConcreto, sender:Address] {
	ein._owner = sender
}

pred met_acceptSharingRequest[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_acceptSharingRequest[ein]
	pre_params_acceptSharingRequest[ein, sender]	
	
	//Post
	eout._currentAuthorizedUser = ein._thirdPartyRequestor
	eout._state = SharingWithThirdParty

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
	eout._init = ein._init
}

pred pre_rejectSharingRequest[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state =  SharingRequestPending// agrego FIX
}

pred pre_params_rejectSharingRequest[ein: EstadoConcreto, sender:Address] {
	ein._owner = sender
}

pred met_rejectSharingRequest[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_rejectSharingRequest[ein]
	pre_params_rejectSharingRequest[ein, sender]

	//Post
	ein._lockerStatus = TextoAvailable
	ein._currentAuthorizedUser = Address0x0
	eout._state = AvailableToShare

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
	eout._init = ein._init
}

pred pre_requestLockerAccess[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state =  AvailableToShare// agrego FIX
}

pred pre_params_requestLockerAccess[ein: EstadoConcreto, sender: Address, intendedPurpose: Texto] {
	ein._owner != sender
}


pred met_requestLockerAccess[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, intendedPurpose: Texto] {
	//Pre
	pre_requestLockerAccess[ein]
	pre_params_requestLockerAccess[ein, sender, intendedPurpose]

	//Post
	eout._thirdPartyRequestor = sender
	eout._intendedPurpose = intendedPurpose
	eout._state = SharingRequestPending

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	//eout._thirdPartyRequestor = ein._thirdPartyRequestor
	//eout._intendedPurpose = ein._intendedPurpose
	eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
	eout._init = ein._init
}

pred pre_releaseLockerAccess[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state =  SharingWithThirdParty// agrego FIX
	some ein._currentAuthorizedUser
}

pred pre_params_releaseLockerAccess[ein: EstadoConcreto, sender: Address] {
	ein._currentAuthorizedUser = sender
}

pred met_releaseLockerAccess[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_releaseLockerAccess[ein]
	pre_params_releaseLockerAccess[ein, sender]

	//Post
	eout._lockerStatus = TextoAvailable
	eout._thirdPartyRequestor = Address0x0
	eout._currentAuthorizedUser = Address0x0
	eout._intendedPurpose = TextoVacio
	eout._state = AvailableToShare

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	//eout._thirdPartyRequestor = ein._thirdPartyRequestor
	//eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
	eout._init = ein._init
}

pred pre_revokeAccessFromThirdParty[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state =  SharingWithThirdParty// agrego FIX
}

pred pre_params_revokeAccessFromThirdParty[ein: EstadoConcreto, sender: Address] {
	ein._owner = sender
}

pred met_revokeAccessFromThirdParty[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_revokeAccessFromThirdParty[ein]
	pre_params_revokeAccessFromThirdParty[ein, sender]

	//Post
	eout._lockerStatus = TextoAvailable
	eout._currentAuthorizedUser = Address0x0
	eout._state = AvailableToShare

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	//eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
	eout._init = ein._init
}

pred pre_terminate[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state !=  Requested and ein._state !=  DocumentReview and ein._state !=  Terminated// agrego FIX
}

pred pre_params_terminate[ein: EstadoConcreto, sender: Address] {
	ein._owner = sender
}

pred met_terminate[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_terminate[ein]
	pre_params_terminate[ein, sender]

	//Post
	eout._currentAuthorizedUser = Address0x0
	eout._state = Terminated

	eout._owner = ein._owner
	eout._bankAgent = ein._bankAgent
	eout._lockerFriendlyName = ein._lockerFriendlyName
	eout._lockerIdentifier = ein._lockerIdentifier
	//eout._currentAuthorizedUser = ein._currentAuthorizedUser
	eout._expirationDate = ein._expirationDate
	eout._image = ein._image
	eout._thirdPartyRequestor = ein._thirdPartyRequestor
	eout._intendedPurpose = ein._intendedPurpose
	eout._lockerStatus = ein._lockerStatus
	eout._rejectionReason = ein._rejectionReason
	//eout._state = ein._state
	eout._init = ein._init
}

// I add a predicate for each possible theoretical partition
pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Requested
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = DocumentReview
}

pred partitionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = AvailableToShare
}

pred partitionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = SharingRequestPending
}

pred partitionS05[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = SharingWithThirdParty
}

pred partitionS06[e: EstadoConcreto]{ // 
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



pred transition__S00__a__S01__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto |
		partitionS00[x] and partitionS01[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v20])
}

pred transition__S00__a__S02__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto |
		partitionS00[x] and partitionS02[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v20])
}

pred transition__S00__a__S03__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto |
		partitionS00[x] and partitionS03[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v20])
}

pred transition__S00__a__S04__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto |
		partitionS00[x] and partitionS04[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v20])
}

pred transition__S00__a__S05__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto |
		partitionS00[x] and partitionS05[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v20])
}

pred transition__S00__a__S06__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto |
		partitionS00[x] and partitionS06[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v20])
}

run transition__S00__a__S01__mediante_met_constructor for 10 EstadoConcreto, 4 Int
run transition__S00__a__S02__mediante_met_constructor for 10 EstadoConcreto, 4 Int
run transition__S00__a__S03__mediante_met_constructor for 10 EstadoConcreto, 4 Int
run transition__S00__a__S04__mediante_met_constructor for 10 EstadoConcreto, 4 Int
run transition__S00__a__S05__mediante_met_constructor for 10 EstadoConcreto, 4 Int
run transition__S00__a__S06__mediante_met_constructor for 10 EstadoConcreto, 4 Int
pred transition__S01__a__S01__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S01__a__S02__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S01__a__S03__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S01__a__S04__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS04[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S01__a__S05__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS05[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S01__a__S06__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS06[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S02__a__S01__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S02__a__S02__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S02__a__S03__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S02__a__S04__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S02__a__S05__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS05[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

pred transition__S02__a__S06__mediante_met_beginReviewProcess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS06[y] and
		v10 != Address0x0 and met_beginReviewProcess[x, y, v10])
}

run transition__S01__a__S01__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S02__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S03__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S04__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S05__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S06__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S01__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S02__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S03__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S04__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S05__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S06__mediante_met_beginReviewProcess for 10 EstadoConcreto, 4 Int
pred transition__S01__a__S01__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S01__a__S02__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S01__a__S03__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S01__a__S04__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS04[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S01__a__S05__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS05[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S01__a__S06__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS06[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S02__a__S01__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S02__a__S02__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S02__a__S03__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S02__a__S04__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S02__a__S05__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS05[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

pred transition__S02__a__S06__mediante_met_uploadDocuments{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS06[y] and
		v10 != Address0x0 and met_uploadDocuments[x, y, v10, v20, v21])
}

run transition__S01__a__S01__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S01__a__S02__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S01__a__S03__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S01__a__S04__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S01__a__S05__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S01__a__S06__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S02__a__S01__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S02__a__S02__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S02__a__S03__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S02__a__S04__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S02__a__S05__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
run transition__S02__a__S06__mediante_met_uploadDocuments for 10 EstadoConcreto, 4 Int
pred transition__S01__a__S01__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S01__a__S02__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S01__a__S03__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S01__a__S04__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS04[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S01__a__S05__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS05[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S01__a__S06__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS01[x] and partitionS06[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S02__a__S01__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S02__a__S02__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S02__a__S03__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S02__a__S04__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S02__a__S05__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS05[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

pred transition__S02__a__S06__mediante_met_shareWithThirdParty{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Texto, v21:Texto |
		partitionS02[x] and partitionS06[y] and
		v10 != Address0x0 and met_shareWithThirdParty[x, y, v10, v11, v20, v21])
}

run transition__S01__a__S01__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S02__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S03__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S04__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S05__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S06__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S01__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S02__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S03__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S04__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S05__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S06__mediante_met_shareWithThirdParty for 10 EstadoConcreto, 4 Int
pred transition__S01__a__S01__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S01__a__S02__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S01__a__S03__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S01__a__S04__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS04[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S01__a__S05__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS05[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S01__a__S06__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS06[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S02__a__S01__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S02__a__S02__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S02__a__S03__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S02__a__S04__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S02__a__S05__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS05[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

pred transition__S02__a__S06__mediante_met_acceptSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS06[y] and
		v10 != Address0x0 and met_acceptSharingRequest[x, y, v10])
}

run transition__S01__a__S01__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S02__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S03__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S04__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S05__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S06__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S01__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S02__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S03__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S04__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S05__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S06__mediante_met_acceptSharingRequest for 10 EstadoConcreto, 4 Int
pred transition__S01__a__S01__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S01__a__S02__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S01__a__S03__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S01__a__S04__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS04[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S01__a__S05__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS05[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S01__a__S06__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS06[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S02__a__S01__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S02__a__S02__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S02__a__S03__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S02__a__S04__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S02__a__S05__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS05[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

pred transition__S02__a__S06__mediante_met_rejectSharingRequest{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS06[y] and
		v10 != Address0x0 and met_rejectSharingRequest[x, y, v10])
}

run transition__S01__a__S01__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S02__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S03__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S04__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S05__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S01__a__S06__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S01__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S02__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S03__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S04__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S05__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
run transition__S02__a__S06__mediante_met_rejectSharingRequest for 10 EstadoConcreto, 4 Int
pred transition__S01__a__S01__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S01__a__S02__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S01__a__S03__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S01__a__S04__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS01[x] and partitionS04[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S01__a__S05__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS01[x] and partitionS05[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S01__a__S06__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS01[x] and partitionS06[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S02__a__S01__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S02__a__S02__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S02__a__S03__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S02__a__S04__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S02__a__S05__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS02[x] and partitionS05[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

pred transition__S02__a__S06__mediante_met_requestLockerAccess{
	(some x,y:EstadoConcreto, v10:Address, v20:Texto |
		partitionS02[x] and partitionS06[y] and
		v10 != Address0x0 and met_requestLockerAccess[x, y, v10, v20])
}

run transition__S01__a__S01__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S02__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S03__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S04__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S05__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S06__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S01__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S02__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S03__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S04__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S05__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S06__mediante_met_requestLockerAccess for 10 EstadoConcreto, 4 Int
pred transition__S01__a__S01__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S01__a__S02__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S01__a__S03__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S01__a__S04__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS04[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S01__a__S05__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS05[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S01__a__S06__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS06[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S02__a__S01__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S02__a__S02__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S02__a__S03__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S02__a__S04__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S02__a__S05__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS05[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

pred transition__S02__a__S06__mediante_met_releaseLockerAccess{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS06[y] and
		v10 != Address0x0 and met_releaseLockerAccess[x, y, v10])
}

run transition__S01__a__S01__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S02__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S03__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S04__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S05__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S01__a__S06__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S01__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S02__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S03__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S04__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S05__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
run transition__S02__a__S06__mediante_met_releaseLockerAccess for 10 EstadoConcreto, 4 Int
pred transition__S01__a__S01__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S01__a__S02__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S01__a__S03__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S01__a__S04__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS04[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S01__a__S05__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS05[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S01__a__S06__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS06[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S02__a__S01__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S02__a__S02__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S02__a__S03__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S02__a__S04__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S02__a__S05__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS05[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

pred transition__S02__a__S06__mediante_met_revokeAccessFromThirdParty{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS06[y] and
		v10 != Address0x0 and met_revokeAccessFromThirdParty[x, y, v10])
}

run transition__S01__a__S01__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S02__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S03__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S04__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S05__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S01__a__S06__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S01__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S02__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S03__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S04__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S05__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
run transition__S02__a__S06__mediante_met_revokeAccessFromThirdParty for 10 EstadoConcreto, 4 Int
pred transition__S01__a__S01__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S01__a__S02__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S01__a__S03__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS03[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S01__a__S04__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS04[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S01__a__S05__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS05[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S01__a__S06__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS06[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S02__a__S01__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S02__a__S02__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S02__a__S03__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S02__a__S04__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S02__a__S05__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS05[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

pred transition__S02__a__S06__mediante_met_terminate{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS06[y] and
		v10 != Address0x0 and met_terminate[x, y, v10])
}

run transition__S01__a__S01__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S01__a__S02__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S01__a__S03__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S01__a__S04__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S01__a__S05__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S01__a__S06__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S02__a__S01__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S02__a__S02__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S02__a__S03__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S02__a__S04__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S02__a__S05__mediante_met_terminate for 10 EstadoConcreto, 4 Int
run transition__S02__a__S06__mediante_met_terminate for 10 EstadoConcreto, 4 Int

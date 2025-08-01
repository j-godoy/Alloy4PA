abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}
one sig AddressD extends Address{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}


abstract sig EstadoConcreto {
	_init: Bool,
	_auctionStart: Int,
	_biddingTime: Int,
	_beneficiary: Address,
	_ended: Bool,
	_highestBidder: Address,
	_highestBid: Int,
	_pendingReturns: Address -> lone Int,
	_blockNumber: Int //lo agrego para simular el paso del tiempo
}


/*
pred invariante[e:EstadoConcreto] {
	//Una Address no puede tener balance negativo
	(no a:Address | a.balance < 0)
	
	(Address0x0 in e._pendingReturns.Int and e._pendingReturns[Address0x0] = 0)
	(all a:Address | a in e._pendingReturns.Int implies e._pendingReturns[a] >= 0)

	e._highestBid >= 0
	highestBidEslaApuestaMayor[e] or e._ended = True
	e._highestBidder in e._pendingReturns.Int

	e._auctionStart >= 0
	e._biddingTime >= 0
}

pred highestBidEslaApuestaMayor[e:EstadoConcreto] {
	(some a1:Address | a1 = e._highestBidder and a1 in e._pendingReturns.Int and
			(all a2:Address | a2 in e._pendingReturns.Int 
						implies e._pendingReturns[a1] >= e._pendingReturns[a2]
							and e._highestBid = e._pendingReturns[a1]
			)
	)
}
*/

pred invariante[e:EstadoConcreto] {
	e._init = True

	e._blockNumber > 0
	e._beneficiary != Address0x0
	
	(Address0x0 in e._pendingReturns.Int and e._pendingReturns[Address0x0] = 0)
	(all a:Address | a in e._pendingReturns.Int implies e._pendingReturns[a] >= 0)

	e._highestBid >= 0
	(e._highestBidder != Address0x0 iff e._highestBid > 0)
	#e._pendingReturns.Int > 1 and not(e._auctionStart.add[e._biddingTime] < e._blockNumber or e._ended = True) => e._highestBid > 0
	#e._pendingReturns.Int > 1 implies e._highestBid > 0
	//highestBidEslaApuestaMayor[e]
	// or e._ended = True
	//e._highestBidder in e._pendingReturns.Int
	e._ended = True implies not (e._blockNumber <= e._auctionStart.add[e._biddingTime])
	e._auctionStart.add[e._biddingTime] < max

	e._auctionStart >= 0
	e._biddingTime >= 0
}

/*pred highestBidEslaApuestaMayor[e:EstadoConcreto] {
	(e._highestBid = 0 and e._pendingReturns = Address0x0->0) or 
	(all a:Address | a in e._pendingReturns.Int
		implies e._pendingReturns[a] <= e._highestBid
	)
}*/

pred pre_constructor[ein:EstadoConcreto] {
	ein._init = False
	ein._auctionStart = 0
	ein._biddingTime = 0
	ein._beneficiary = Address0x0
	ein._ended = False
	ein._highestBidder = Address0x0
	ein._highestBid = 0
	ein._pendingReturns = Address0x0 -> 0
	ein._blockNumber >= 0
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address,
				beneficiary: Address, auctionStart: Int, biddingTime: Int] {
	auctionStart >= 0
	biddingTime >= 0
	beneficiary != Address0x0
	auctionStart.add[biddingTime] < max
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
				beneficiary: Address, auctionStart: Int, biddingTime: Int] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, beneficiary, auctionStart, biddingTime]

	//Post
	eout._auctionStart = auctionStart
	eout._biddingTime = biddingTime
	eout._beneficiary = beneficiary
	eout._init = True

	//eout._auctionStart = ein._auctionStart
	//eout._biddingTime = ein._biddingTime
	//eout._beneficiary = ein._beneficiary
	eout._ended = ein._ended
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber
}

pred pre_bid[ein:EstadoConcreto] {
	ein._init = True
	not(ein._auctionStart.add[ein._biddingTime] < ein._blockNumber or ein._ended = True)
	(ein._beneficiary != Address0x0)
}

pred pre_params_bid[ein: EstadoConcreto, sender:Address, value: Int] {
	sender != Address0x0
	not(value <= ein._highestBid)
}

pred met_bid[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int] {
	//PRE
	pre_bid[ein]
	pre_params_bid[ein, sender, value]

	//POST
	eout._pendingReturns = ein._pendingReturns++ein._highestBidder->ein._pendingReturns[ein._highestBidder].add[ein._highestBid]
	eout._highestBidder = sender
	eout._highestBid = value

	eout._init = ein._init
	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._ended = ein._ended
	//eout._highestBidder = ein._highestBidder
	//eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber
}

pred pre_withdraw[ein: EstadoConcreto] {
	ein._init = True
	some a:Address | a !=Address0x0 and a in ein._pendingReturns.Int
				and ein._pendingReturns[a] != 0
	(ein._beneficiary != Address0x0)
}

pred pre_params_withdraw[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
	sender in ein._pendingReturns.Int and ein._pendingReturns[sender] > 0
}

pred met_withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_withdraw[ein]
	pre_params_withdraw[ein, sender]

	//POST

	//(let pr = pendingReturns[sender] |
	eout._pendingReturns = ein._pendingReturns++sender -> 0

	eout._init = ein._init
	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._ended = ein._ended
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber
}

pred pre_auctionEnd[ein: EstadoConcreto] {
	ein._init = True
	not (ein._blockNumber <= ein._auctionStart.add[ein._biddingTime]
		or ein._ended = True) //FIX
	//or ein._ended = False) //BUG
	(ein._beneficiary != Address0x0)
}

pred pre_params_auctionEnd[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
}

pred met_auctionEnd[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_auctionEnd[ein]
	pre_params_auctionEnd[ein, sender]

	//POST
	eout._ended = True
	eout._beneficiary = ein._beneficiary
	//eout._beneficiary.balance = ein._beneficiary.balance.add[ein._highestBid]

	eout._init = ein._init
	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	//eout._beneficiary = ein._beneficiary
	//eout._ended = ein._ended
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber
}

pred pre_t[ein:EstadoConcreto] {
	ein._init = True
}

pred pre_params_t[ein: EstadoConcreto, sender:Address] {
}

pred met_t[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_t[ein]
	pre_params_t[ein, sender]
	
	eout._init = ein._init
	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._ended = ein._ended
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	// eout._blockNumber = ein._blockNumber.add[1]
	ein._blockNumber < max => eout._blockNumber = ein._blockNumber.add[1] else eout._blockNumber = ein._blockNumber
}


//////////////////////////////////////////////////////////////////////////////////////
// I add a predicate for each possible theoretical partition //
//////////////////////////////////////////////////////////////////////////////////////


pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}

pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
	e._ended = True
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
	e._ended = True
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
	e._ended = True
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
	e._ended = True
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
	e._ended = True
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
	e._ended = True
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
	e._ended = True
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
	e._ended = True
}

pred partitionS09[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
	e._ended = True
}

pred partitionS10[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
	e._ended = True
}

pred partitionS11[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
	e._ended = True
}

pred partitionS12[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
	e._ended = True
}

pred partitionS13[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
	e._ended = True
}

pred partitionS14[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
	e._ended = True
}

pred partitionS15[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
	e._ended = True
}

pred partitionS16[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
	e._ended = True
}

pred partitionS17[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
	e._ended = False
}

pred partitionS18[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
	e._ended = False
}

pred partitionS19[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
	e._ended = False
}

pred partitionS20[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
	e._ended = False
}

pred partitionS21[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
	e._ended = False
}

pred partitionS22[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
	e._ended = False
}

pred partitionS23[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
	e._ended = False
}

pred partitionS24[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
	e._ended = False
}

pred partitionS25[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
	e._ended = False
}

pred partitionS26[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
	e._ended = False
}

pred partitionS27[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
	e._ended = False
}

pred partitionS28[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
	e._ended = False
}

pred partitionS29[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
	e._ended = False
}

pred partitionS30[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
	e._ended = False
}

pred partitionS31[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
	e._ended = False
}

pred partitionS32[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
	e._ended = False
}




//======predicates for blue queries======



pred blue_transition__S22__a__S22__mediante_met_t {
	some x: EstadoConcreto | partitionS22[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS22[y]))
}
run blue_transition__S22__a__S22__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S20__a__S20__mediante_met_bid {
	some x: EstadoConcreto | partitionS20[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS20[y]))
}
run blue_transition__S20__a__S20__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S22__a__S12__mediante_met_auctionEnd {
	some x: EstadoConcreto | partitionS22[x] and (not pre_auctionEnd[x] or (all sender:{this/Address} | pre_params_auctionEnd[x,sender] implies some y:EstadoConcreto | met_auctionEnd[x,y,sender] and not partitionS12[y]))
}
run blue_transition__S22__a__S12__mediante_met_auctionEnd for 10 EstadoConcreto

pred blue_transition__S18__a__S18__mediante_met_t {
	some x: EstadoConcreto | partitionS18[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS18[y]))
}
run blue_transition__S18__a__S18__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S00__a__S22__mediante_met_constructor {
	some x: EstadoConcreto | partitionS00[x] and ((all sender:{this/Address}, beneficiary:{this/Address}, auctionStart:{Int}, biddingTime:{Int} | pre_params_constructor[x,sender, beneficiary, auctionStart, biddingTime] implies some y:EstadoConcreto | met_constructor[x,y,sender, beneficiary, auctionStart, biddingTime] and not partitionS22[y]))
}
run blue_transition__S00__a__S22__mediante_met_constructor for 10 EstadoConcreto

pred blue_transition__S00__a__S25__mediante_met_constructor {
	some x: EstadoConcreto | partitionS00[x] and ((all sender:{this/Address}, beneficiary:{this/Address}, auctionStart:{Int}, biddingTime:{Int} | pre_params_constructor[x,sender, beneficiary, auctionStart, biddingTime] implies some y:EstadoConcreto | met_constructor[x,y,sender, beneficiary, auctionStart, biddingTime] and not partitionS25[y]))
}
run blue_transition__S00__a__S25__mediante_met_constructor for 10 EstadoConcreto

pred blue_transition__S07__a__S07__mediante_met_t {
	some x: EstadoConcreto | partitionS07[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS07[y]))
}
run blue_transition__S07__a__S07__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S07__a__S07__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS07[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS07[y]))
}
run blue_transition__S07__a__S07__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S07__a__S12__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS07[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS12[y]))
}
run blue_transition__S07__a__S12__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S18__a__S18__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS18[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS18[y]))
}
run blue_transition__S18__a__S18__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S18__a__S22__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS18[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS22[y]))
}
run blue_transition__S18__a__S22__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S25__a__S20__mediante_met_bid {
	some x: EstadoConcreto | partitionS25[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS20[y]))
}
run blue_transition__S25__a__S20__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S25__a__S25__mediante_met_bid {
	some x: EstadoConcreto | partitionS25[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS25[y]))
}
run blue_transition__S25__a__S25__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S20__a__S18__mediante_met_t {
	some x: EstadoConcreto | partitionS20[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS18[y]))
}
run blue_transition__S20__a__S18__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S20__a__S20__mediante_met_t {
	some x: EstadoConcreto | partitionS20[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS20[y]))
}
run blue_transition__S20__a__S20__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S20__a__S20__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS20[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS20[y]))
}
run blue_transition__S20__a__S20__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S20__a__S25__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS20[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS25[y]))
}
run blue_transition__S20__a__S25__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S18__a__S07__mediante_met_auctionEnd {
	some x: EstadoConcreto | partitionS18[x] and (not pre_auctionEnd[x] or (all sender:{this/Address} | pre_params_auctionEnd[x,sender] implies some y:EstadoConcreto | met_auctionEnd[x,y,sender] and not partitionS07[y]))
}
run blue_transition__S18__a__S07__mediante_met_auctionEnd for 10 EstadoConcreto

pred blue_transition__S12__a__S12__mediante_met_t {
	some x: EstadoConcreto | partitionS12[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS12[y]))
}
run blue_transition__S12__a__S12__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S25__a__S22__mediante_met_t {
	some x: EstadoConcreto | partitionS25[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS22[y]))
}
run blue_transition__S25__a__S22__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S25__a__S25__mediante_met_t {
	some x: EstadoConcreto | partitionS25[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS25[y]))
}
run blue_transition__S25__a__S25__mediante_met_t for 10 EstadoConcreto




//======predicates for turquoise queries======



pred turquoise_transition__S18__a__S18_S22__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS18[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS18[y] and not partitionS22[y]))
}
run turquoise_transition__S18__a__S18_S22__mediante_met_withdraw for 10 EstadoConcreto

pred turquoise_transition__S20__a__S20_S25__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS20[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS20[y] and not partitionS25[y]))
}
run turquoise_transition__S20__a__S20_S25__mediante_met_withdraw for 10 EstadoConcreto

pred turquoise_transition__S20__a__S18_S20__mediante_met_t {
	some x: EstadoConcreto | partitionS20[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS18[y] and not partitionS20[y]))
}
run turquoise_transition__S20__a__S18_S20__mediante_met_t for 10 EstadoConcreto

pred turquoise_transition__S25__a__S22_S25__mediante_met_t {
	some x: EstadoConcreto | partitionS25[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS22[y] and not partitionS25[y]))
}
run turquoise_transition__S25__a__S22_S25__mediante_met_t for 10 EstadoConcreto

pred turquoise_transition__S07__a__S07_S12__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS07[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS07[y] and not partitionS12[y]))
}
run turquoise_transition__S07__a__S07_S12__mediante_met_withdraw for 10 EstadoConcreto


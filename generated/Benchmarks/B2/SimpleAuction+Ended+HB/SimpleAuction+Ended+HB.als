abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressBeneficiary extends Address{}

//run transicion_S00_a_INV_mediante_met_constructor for 2 EstadoConcreto// concrete states
abstract sig EstadoConcreto {
	_auctionStart: Int,
	_biddingTime: Int,
	_beneficiary: Address,
	_highestBidder: Address,
	_highestBid: Int,
	_pendingReturns: Address -> lone Int,
	_ended: Bool,
	_now: Int, //lo agrego para simular el paso del tiempo
	_init: Bool
}

pred invariante[e:EstadoConcreto] {	
	e._init = True
	(Address0x0 in e._pendingReturns.Int and e._pendingReturns[Address0x0] = 0)
	(all a:Address | a in e._pendingReturns.Int implies e._pendingReturns[a] >= 0)

	e._highestBid >= 0
//	highestBidEslaApuestaMayor[e] or #(e._pendingReturns.Int) = 1 //or e._ended = True

	e._auctionStart >= 0
	e._biddingTime >= 0
	
	e._highestBidder = Address0x0 implies #(e._pendingReturns.Int) = 1

	e._ended = True implies e._now >= e._auctionStart.add[e._biddingTime]
	e._auctionStart.add[e._biddingTime] < max and e._auctionStart.add[e._biddingTime] >= 0
	e._beneficiary = AddressBeneficiary
}

/*pred highestBidEslaApuestaMayor[e:EstadoConcreto] {
	(some a1:Address | a1 = e._highestBidder and a1 !in e._pendingReturns.Int and
			(all a2:Address | a2 in e._pendingReturns.Int implies
				e._highestBid >= e._pendingReturns[a2]
			)
	) or
	(some a1:Address | a1 = e._highestBidder and e._highestBid>0 and a1 in e._pendingReturns.Int and
		(all a2:Address | a2 in e._pendingReturns.Int implies
				e._pendingReturns[a1] >= e._pendingReturns[a2]
		)
	)
}*/

pred pre_constructor[ein: EstadoConcreto] {
	ein._beneficiary = Address0x0
	ein._highestBidder = Address0x0
	ein._highestBid = 0
	ein._pendingReturns = Address0x0 -> 0
	ein._ended = False
	ein._init = False
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address, biddingTime: Int ] {
	biddingTime >= 0
	sender != Address0x0
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, biddingTime: Int ] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, biddingTime]

	//Post
	eout._auctionStart = 1
	eout._beneficiary = AddressBeneficiary
	eout._biddingTime = biddingTime
	eout._init = True


	//eout._auctionStart = ein._auctionStart
	//eout._biddingTime = ein._biddingTime
	//eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now
}

pred pre_bid[ein:EstadoConcreto] {
	ein._now <= ein._auctionStart.add[ein._biddingTime]
	ein._init = True
}

pred pre_params_bid[ein: EstadoConcreto, sender:Address, value: Int] {
	sender != Address0x0
	ein._highestBid < max => value > ein._highestBid else value = ein._highestBid
}

pred met_bid[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int] {
	//PRE
	pre_bid[ein]
	pre_params_bid[ein, sender, value]
	

	//POST
	ein._highestBidder != Address0x0 =>
		(eout._pendingReturns = ein._pendingReturns++ein._highestBidder->ein._pendingReturns[ein._highestBidder].add[ein._highestBid])
	else
		(eout._pendingReturns = ein._pendingReturns)
	
	eout._highestBidder = sender
	eout._highestBid = value

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	//eout._highestBidder = ein._highestBidder
	//eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now
	eout._init = ein._init
}

pred pre_withdraw[ein: EstadoConcreto] {
	//highestBidEslaApuestaMayor[ein]
	some a:Address | a !=Address0x0 and a in ein._pendingReturns.Int
				and ein._pendingReturns[a] != 0
	//(ein._beneficiary != Address0x0)
	ein._init = True
}

pred pre_params_withdraw[ein: EstadoConcreto, sender: Address] {
	ein._pendingReturns[sender] > 0
	sender != Address0x0
	sender in ein._pendingReturns.Int
}

pred met_withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_withdraw[ein]
	pre_params_withdraw[ein, sender]

	//POST

	//(let pr = pendingReturns[sender] |
	eout._pendingReturns = ein._pendingReturns++sender -> 0

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now
	eout._init = ein._init
}

pred pre_auctionEnd[ein: EstadoConcreto] {
	(ein._now >= (ein._auctionStart.add[ein._biddingTime])) // auction did not yet end
	(ein._ended = False)
	ein._init = True
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
	//eout._beneficiary.balance = ein._beneficiary.balance.add[ein._highestBid]

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	//eout._ended = ein._ended
	eout._now = ein._now
	eout._init = ein._init
}

pred pre_t[e:EstadoConcreto] {
	e._init = True
}

pred pre_params_t[ein: EstadoConcreto, sender:Address] {
	// timeElapsed >= 0
}

pred met_t[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_t[ein]
	pre_params_t[ein, sender]
	
	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	ein._now < max => eout._now = ein._now.add[1] else eout._now = ein._now
	eout._init = ein._init	
}


//////////////////////////////////////////////////////////////////////////////////////
// I add a predicate for each possible theoretical partition //
//////////////////////////////////////////////////////////////////////////////////////
pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}


pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder = Address0x0)
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	//(some a:Address | a in e._pendingReturns.Int and a = AddressA and e._highestBidder = a)
	e._highestBidder = AddressA
}

pred partitionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = False)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	//(some b:Address | b in e._pendingReturns.Int and b != AddressA and e._highestBidder = b)
	e._highestBidder != AddressA
}


pred partitionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder = Address0x0)
}

pred partitionS05[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	//(some a:Address | a in e._pendingReturns.Int and a = AddressA and e._highestBidder = a)
	e._highestBidder = AddressA
}

pred partitionS06[e: EstadoConcreto]{ // 
	(invariante[e])
	(e._ended = True)
	(e._beneficiary != Address0x0)
	(e._highestBidder != Address0x0)
	//(some b:Address | b in e._pendingReturns.Int and b != AddressA and e._highestBidder = b)
	e._highestBidder != AddressA
}



//======predicates for blue queries======



pred blue_transition__S01__a__S02__mediante_met_bid {
	some x: EstadoConcreto | partitionS01[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS02[y]))
}
run blue_transition__S01__a__S02__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S01__a__S03__mediante_met_bid {
	some x: EstadoConcreto | partitionS01[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS03[y]))
}
run blue_transition__S01__a__S03__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S06__a__S05__mediante_met_bid {
	some x: EstadoConcreto | partitionS06[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS05[y]))
}
run blue_transition__S06__a__S05__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S06__a__S06__mediante_met_bid {
	some x: EstadoConcreto | partitionS06[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS06[y]))
}
run blue_transition__S06__a__S06__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S05__a__S05__mediante_met_t {
	some x: EstadoConcreto | partitionS05[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS05[y]))
}
run blue_transition__S05__a__S05__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S01__a__S01__mediante_met_t {
	some x: EstadoConcreto | partitionS01[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS01[y]))
}
run blue_transition__S01__a__S01__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S03__a__S03__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS03[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS03[y]))
}
run blue_transition__S03__a__S03__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S06__a__S06__mediante_met_t {
	some x: EstadoConcreto | partitionS06[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS06[y]))
}
run blue_transition__S06__a__S06__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S04__a__S04__mediante_met_t {
	some x: EstadoConcreto | partitionS04[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS04[y]))
}
run blue_transition__S04__a__S04__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S04__a__S05__mediante_met_bid {
	some x: EstadoConcreto | partitionS04[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS05[y]))
}
run blue_transition__S04__a__S05__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S04__a__S06__mediante_met_bid {
	some x: EstadoConcreto | partitionS04[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS06[y]))
}
run blue_transition__S04__a__S06__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S03__a__S03__mediante_met_t {
	some x: EstadoConcreto | partitionS03[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS03[y]))
}
run blue_transition__S03__a__S03__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S01__a__S04__mediante_met_auctionEnd {
	some x: EstadoConcreto | partitionS01[x] and (not pre_auctionEnd[x] or (all sender:{this/Address} | pre_params_auctionEnd[x,sender] implies some y:EstadoConcreto | met_auctionEnd[x,y,sender] and not partitionS04[y]))
}
run blue_transition__S01__a__S04__mediante_met_auctionEnd for 10 EstadoConcreto

pred blue_transition__S06__a__S06__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS06[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS06[y]))
}
run blue_transition__S06__a__S06__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S02__a__S02__mediante_met_bid {
	some x: EstadoConcreto | partitionS02[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS02[y]))
}
run blue_transition__S02__a__S02__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S02__a__S03__mediante_met_bid {
	some x: EstadoConcreto | partitionS02[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS03[y]))
}
run blue_transition__S02__a__S03__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S02__a__S02__mediante_met_t {
	some x: EstadoConcreto | partitionS02[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS02[y]))
}
run blue_transition__S02__a__S02__mediante_met_t for 10 EstadoConcreto

pred blue_transition__S00__a__S01__mediante_met_constructor {
	some x: EstadoConcreto | partitionS00[x] and ((all sender:{this/Address}, biddingTime:{Int} | pre_params_constructor[x,sender, biddingTime] implies some y:EstadoConcreto | met_constructor[x,y,sender, biddingTime] and not partitionS01[y]))
}
run blue_transition__S00__a__S01__mediante_met_constructor for 10 EstadoConcreto

pred blue_transition__S05__a__S05__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS05[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS05[y]))
}
run blue_transition__S05__a__S05__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S05__a__S05__mediante_met_bid {
	some x: EstadoConcreto | partitionS05[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS05[y]))
}
run blue_transition__S05__a__S05__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S05__a__S06__mediante_met_bid {
	some x: EstadoConcreto | partitionS05[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS06[y]))
}
run blue_transition__S05__a__S06__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S03__a__S06__mediante_met_auctionEnd {
	some x: EstadoConcreto | partitionS03[x] and (not pre_auctionEnd[x] or (all sender:{this/Address} | pre_params_auctionEnd[x,sender] implies some y:EstadoConcreto | met_auctionEnd[x,y,sender] and not partitionS06[y]))
}
run blue_transition__S03__a__S06__mediante_met_auctionEnd for 10 EstadoConcreto

pred blue_transition__S03__a__S02__mediante_met_bid {
	some x: EstadoConcreto | partitionS03[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS02[y]))
}
run blue_transition__S03__a__S02__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S03__a__S03__mediante_met_bid {
	some x: EstadoConcreto | partitionS03[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int} | pre_params_bid[x,sender, value] implies some y:EstadoConcreto | met_bid[x,y,sender, value] and not partitionS03[y]))
}
run blue_transition__S03__a__S03__mediante_met_bid for 10 EstadoConcreto

pred blue_transition__S02__a__S02__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS02[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS02[y]))
}
run blue_transition__S02__a__S02__mediante_met_withdraw for 10 EstadoConcreto

pred blue_transition__S02__a__S05__mediante_met_auctionEnd {
	some x: EstadoConcreto | partitionS02[x] and (not pre_auctionEnd[x] or (all sender:{this/Address} | pre_params_auctionEnd[x,sender] implies some y:EstadoConcreto | met_auctionEnd[x,y,sender] and not partitionS05[y]))
}
run blue_transition__S02__a__S05__mediante_met_auctionEnd for 10 EstadoConcreto




//======predicates for turquoise queries======




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
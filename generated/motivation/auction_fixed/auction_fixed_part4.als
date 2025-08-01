abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}

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
	_balance: Int,
	_ownerFee: Int,
	_pendingReturns: Bidders,
	_blockNumber: Int, //lo agrego para simular el paso del tiempo
	_owner: Address,
}

sig Bidders{b: Address->lone Int}
fun LIMIT[]: Int {3}

pred invariante[e:EstadoConcreto] {
	e._init = True
	
	e._blockNumber > 0
	e._beneficiary != Address0x0
	e._owner != Address0x0
	e._balance >= 0
	e._ownerFee >= 0

	(Address0x0 in e._pendingReturns.b.Int and e._pendingReturns.b[Address0x0] = 0)
	(all a:Address | a in e._pendingReturns.b.Int implies e._pendingReturns.b[a] >= 0)

	e._highestBid >= 0
	(e._highestBidder != Address0x0 iff e._highestBid > 0)
	#e._pendingReturns.b.Int > 1 and not(e._auctionStart.add[e._biddingTime] < e._blockNumber or e._ended = True) => e._highestBid > 0
	#e._pendingReturns.b.Int > 1 implies e._highestBid > 0

	e._ended = False implies sumatoria[e._pendingReturns, e._balance.minus[e._highestBid]]
	e._ended = True implies sumatoria[e._pendingReturns, e._balance]//fix

	e._ended = True implies not (e._blockNumber < e._auctionStart.add[e._biddingTime])
	e._auctionStart.add[e._biddingTime] < max
	e._highestBid.add[e._ownerFee] < max
	e._ownerFee <= e._highestBid

	e._owner !in e._pendingReturns.b.Int
	e._owner != e._highestBidder
	e._beneficiary !in e._pendingReturns.b.Int
	e._beneficiary != e._highestBidder

	e._auctionStart >= 0
	e._biddingTime >= 0

	//fixed size: Int= 0,1,2,3; max length=4
	all d0:Address | e._pendingReturns.b[d0] >= 0 and e._pendingReturns.b[d0] <= 2//LIMIT[]
	// #(e._pendingReturns.b.Int) <= LIMIT[]

	all s:SumatoriaSeq, i:Int | some s.sec[i] implies s.sec[i] >= 0
	some s:SumatoriaSeq | s.sec = 0->0
	some s:SumatoriaSeq | s.sec = 0->0+1->0
	some s:SumatoriaSeq | s.sec = 0->0+1->0+2->0
	some s:SumatoriaSeq | s.sec = 0->1
	some s:SumatoriaSeq | s.sec = 0->1+1->0
	some s:SumatoriaSeq | s.sec = 0->1+1->0+2->0
	some s:SumatoriaSeq | s.sec = 0->2
	some s:SumatoriaSeq | s.sec = 0->2+1->0
	some s:SumatoriaSeq | s.sec = 0->2+1->0+2->0
}

fun sumof[s:seq Int]: Int {
	s=none->none implies 0
	else s=0->0 implies 0
	else s=0->1 implies 1
	else s=0->2 implies 2
	else s=0->3 implies 3
	else s=0->0+1->0 implies 0
	else s=0->0+1->1 implies 1
	else s=0->0+1->2 implies 2
	else s=0->0+1->3 implies 3
	else s=0->1+1->0 implies 1
	else s=0->1+1->1 implies 2
	else s=0->1+1->2 implies 3
	else s=0->1+1->3 implies 4
	else s=0->2+1->0 implies 2
	else s=0->2+1->1 implies 3
	else s=0->2+1->2 implies 4
	else s=0->2+1->3 implies 5
	else s=0->3+1->0 implies 3
	else s=0->3+1->1 implies 4
	else s=0->3+1->2 implies 5
	else s=0->3+1->3 implies 6
	else s=0->0+1->0+2->0 implies 0
	else s=0->0+1->0+2->1 implies 1
	else s=0->0+1->0+2->2 implies 2
	else s=0->0+1->0+2->3 implies 3
	else s=0->0+1->1+2->0 implies 1
	else s=0->0+1->1+2->1 implies 2
	else s=0->0+1->1+2->2 implies 3
	else s=0->0+1->1+2->3 implies 4
	else s=0->0+1->2+2->0 implies 2
	else s=0->0+1->2+2->1 implies 3
	else s=0->0+1->2+2->2 implies 4
	else s=0->0+1->2+2->3 implies 5
	else s=0->0+1->3+2->0 implies 3
	else s=0->0+1->3+2->1 implies 4
	else s=0->0+1->3+2->2 implies 5
	else s=0->0+1->3+2->3 implies 6
	else s=0->1+1->0+2->0 implies 1
	else s=0->1+1->0+2->1 implies 2
	else s=0->1+1->0+2->2 implies 3
	else s=0->1+1->0+2->3 implies 4
	else s=0->1+1->1+2->0 implies 2
	else s=0->1+1->1+2->1 implies 3
	else s=0->1+1->1+2->2 implies 4
	else s=0->1+1->1+2->3 implies 5
	else s=0->1+1->2+2->0 implies 3
	else s=0->1+1->2+2->1 implies 4
	else s=0->1+1->2+2->2 implies 5
	else s=0->1+1->2+2->3 implies 6
	else s=0->1+1->3+2->0 implies 4
	else s=0->1+1->3+2->1 implies 5
	else s=0->1+1->3+2->2 implies 6
	else s=0->1+1->3+2->3 implies 7
	else s=0->2+1->0+2->0 implies 2
	else s=0->2+1->0+2->1 implies 3
	else s=0->2+1->0+2->2 implies 4
	else s=0->2+1->0+2->3 implies 5
	else s=0->2+1->1+2->0 implies 3
	else s=0->2+1->1+2->1 implies 4
	else s=0->2+1->1+2->2 implies 5
	else s=0->2+1->1+2->3 implies 6
	else s=0->2+1->2+2->0 implies 4
	else s=0->2+1->2+2->1 implies 5
	else s=0->2+1->2+2->2 implies 6
	else s=0->2+1->2+2->3 implies 7
	else s=0->2+1->3+2->0 implies 5
	else s=0->2+1->3+2->1 implies 6
	else s=0->2+1->3+2->2 implies 7
	else s=0->2+1->3+2->3 implies 8
	else s=0->3+1->0+2->0 implies 3
	else s=0->3+1->0+2->1 implies 4
	else s=0->3+1->0+2->2 implies 5
	else s=0->3+1->0+2->3 implies 6
	else s=0->3+1->1+2->0 implies 4
	else s=0->3+1->1+2->1 implies 5
	else s=0->3+1->1+2->2 implies 6
	else s=0->3+1->1+2->3 implies 7
	else s=0->3+1->2+2->0 implies 5
	else s=0->3+1->2+2->1 implies 6
	else s=0->3+1->2+2->2 implies 7
	else s=0->3+1->2+2->3 implies 8
	else s=0->3+1->3+2->0 implies 6
	else s=0->3+1->3+2->1 implies 7
	else s=0->3+1->3+2->2 implies 8
	else s=0->3+1->3+2->3 implies 9
	else 0
}

pred sumatoria [s: set Bidders, suma: Int] {
	some sumaSeq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
}

pred sumatoriaSubSeq [s: set Bidders, suma: Int] {
	some sumaSeq: SumatoriaSeq, subseq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and
			subSeq[sumaSeq.sec, subseq.sec] and sumof[subseq.sec] = suma
}

pred subSeq [original: seq Int, subseq: seq Int] {
	#subseq <= #original
	all i: Int | some subseq[i] implies subseq[i] in original.elems
	all i: Int | some subseq[i] implies #subseq.i <= #original.i
}

pred toSeq [s: set Bidders, ret: seq Int] {
	all d0: s.b.Int | some i: Int | ret[i]=s.b[d0] //Todo elemento del set está en la seq
	all i: Int | some ret[i] implies some d0: s.b.Int | s.b[d0]=ret[i]//Todo elemento de la seq está en el set
	all i: Int | #(s.b.i) = #(ret.i) //#elem(set,e) = #elem(seq,e)
	#(s.b.Int)=#(ret)
}


sig SumatoriaSeq {sec: seq Int}

pred pre_constructor[ein:EstadoConcreto] {
	ein._init = False
	ein._auctionStart = 0
	ein._biddingTime = 0
	ein._beneficiary = Address0x0
	ein._ended = False
	ein._balance = 0
	ein._ownerFee = 0
	ein._highestBidder = Address0x0
	ein._highestBid = 0
	ein._pendingReturns.b = Address0x0 -> 0
	ein._blockNumber >= 0
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address,
				beneficiary: Address, auctionStart: Int, biddingTime: Int, ownerFee: Int] {
	auctionStart >= 0
	biddingTime >= 0
	beneficiary != Address0x0
	sender != Address0x0 //and sender != AddressA
	auctionStart.add[biddingTime] < max
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
				beneficiary: Address, auctionStart: Int, biddingTime: Int, ownerFee: Int] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, beneficiary, auctionStart, biddingTime, ownerFee]

	//Post
	eout._auctionStart = auctionStart
	eout._biddingTime = biddingTime
	eout._beneficiary = beneficiary
	eout._init = True
	eout._owner = sender
	eout._ownerFee = ownerFee

	eout._ended = ein._ended
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}

pred pre_bid[ein:EstadoConcreto] {
	ein._init = True
	ein._auctionStart.add[ein._biddingTime] > ein._blockNumber
	ein._ended = False
	(ein._beneficiary != Address0x0)
}

pred pre_params_bid[ein: EstadoConcreto, sender:Address, value: Int] {
	sender != Address0x0
	sender != ein._owner
	not(value < ein._highestBid)
}

pred met_bid[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int] {
	//PRE
	pre_bid[ein]
	pre_params_bid[ein, sender, value]

	//POST
	eout._pendingReturns.b = ein._pendingReturns.b++ein._highestBidder->ein._pendingReturns.b[ein._highestBidder].add[ein._highestBid]
	eout._highestBidder = sender
	eout._highestBid = value

	eout._init = ein._init
	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._ended = ein._ended
	eout._blockNumber = ein._blockNumber
	eout._owner = ein._owner
	eout._ownerFee = ein._ownerFee
}

pred pre_withdraw[ein: EstadoConcreto] {
	ein._init = True
	some a:Address | a !=Address0x0 and a in ein._pendingReturns.b.Int
				and ein._pendingReturns.b[a] > 0
	(ein._beneficiary != Address0x0)
	ein._blockNumber >= ein._auctionStart.add[ein._biddingTime]
}

pred pre_params_withdraw[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
	sender in ein._pendingReturns.b.Int and ein._pendingReturns.b[sender] > 0
	//not precondition in code, but will revert if not enough balance
	ein._balance >= ein._pendingReturns.b[sender]
}


pred met_withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_withdraw[ein]
	pre_params_withdraw[ein, sender]

	//POST

	eout._pendingReturns.b = ein._pendingReturns.b++sender -> 0
	eout._balance = ein._balance.minus[ein._pendingReturns.b[sender]]

	eout._init = ein._init
	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._ended = ein._ended
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._blockNumber = ein._blockNumber
	eout._owner = ein._owner
	eout._ownerFee = ein._ownerFee
}

pred pre_auctionEnd[ein: EstadoConcreto] {
	ein._init = True
	ein._blockNumber >= ein._auctionStart.add[ein._biddingTime]
	ein._ended = False //FIX
	(ein._beneficiary != Address0x0)
}

pred pre_params_auctionEnd[ein:EstadoConcreto, sender:Address] {
	sender != Address0x0
	sender = ein._beneficiary
	//not precondition in code, but it will revert if not enough balance
	// ein._balance >= ein._ownerFee.add[ein._highestBid]//Bug
	ein._balance >= ein._highestBid//Fix
}

pred met_auctionEnd[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_auctionEnd[ein]
	pre_params_auctionEnd[ein, sender]

	// ein._balance >= ein._ownerFee.add[ein._highestBid] =>
    // 	(eout._balance = ein._balance.minus[ein._ownerFee].minus[ein._highestBid])
    // else
    (eout._balance = ein._balance.minus[ein._highestBid])

	//POST
	eout._ended = True
	eout._beneficiary = ein._beneficiary

	eout._init = ein._init
	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._blockNumber = ein._blockNumber
	eout._owner = ein._owner
	eout._ownerFee = ein._ownerFee
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
	ein._blockNumber < max => eout._blockNumber = ein._blockNumber.add[1] else eout._blockNumber = ein._blockNumber
	eout._owner = ein._owner
	eout._balance = ein._balance
	eout._ownerFee = ein._ownerFee
}


//////////////////////////////////////////////////////////////////////////////////////
// Partitions //
//////////////////////////////////////////////////////////////////////////////////////

pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}


pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS09[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
}

pred partitionS10[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS11[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS12[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
}

pred partitionS13[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS14[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS15[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS16[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
}




pred transition__S07__a__S02__mediante_met_bid{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS07[x] and partitionS02[y] and
		v10 != Address0x0 and met_bid[x, y, v10, v20])
}

pred transition__S07__a__S06__mediante_met_bid{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS07[x] and partitionS06[y] and
		v10 != Address0x0 and met_bid[x, y, v10, v20])
}

pred transition__S07__a__S07__mediante_met_bid{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS07[x] and partitionS07[y] and
		v10 != Address0x0 and met_bid[x, y, v10, v20])
}

pred transition__S07__a__S09__mediante_met_bid{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS07[x] and partitionS09[y] and
		v10 != Address0x0 and met_bid[x, y, v10, v20])
}

pred transition__S07__a__S12__mediante_met_bid{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS07[x] and partitionS12[y] and
		v10 != Address0x0 and met_bid[x, y, v10, v20])
}

run transition__S07__a__S02__mediante_met_bid for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S06__mediante_met_bid for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S07__mediante_met_bid for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S09__mediante_met_bid for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S12__mediante_met_bid for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
pred transition__S07__a__S02__mediante_met_withdraw{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS02[y] and
		v10 != Address0x0 and met_withdraw[x, y, v10])
}

pred transition__S07__a__S06__mediante_met_withdraw{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS06[y] and
		v10 != Address0x0 and met_withdraw[x, y, v10])
}

pred transition__S07__a__S07__mediante_met_withdraw{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS07[y] and
		v10 != Address0x0 and met_withdraw[x, y, v10])
}

pred transition__S07__a__S09__mediante_met_withdraw{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS09[y] and
		v10 != Address0x0 and met_withdraw[x, y, v10])
}

pred transition__S07__a__S12__mediante_met_withdraw{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS12[y] and
		v10 != Address0x0 and met_withdraw[x, y, v10])
}

run transition__S07__a__S02__mediante_met_withdraw for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S06__mediante_met_withdraw for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S07__mediante_met_withdraw for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S09__mediante_met_withdraw for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S12__mediante_met_withdraw for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
pred transition__S07__a__S02__mediante_met_auctionEnd{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS02[y] and
		v10 != Address0x0 and met_auctionEnd[x, y, v10])
}

pred transition__S07__a__S06__mediante_met_auctionEnd{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS06[y] and
		v10 != Address0x0 and met_auctionEnd[x, y, v10])
}

pred transition__S07__a__S07__mediante_met_auctionEnd{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS07[y] and
		v10 != Address0x0 and met_auctionEnd[x, y, v10])
}

pred transition__S07__a__S09__mediante_met_auctionEnd{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS09[y] and
		v10 != Address0x0 and met_auctionEnd[x, y, v10])
}

pred transition__S07__a__S12__mediante_met_auctionEnd{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS12[y] and
		v10 != Address0x0 and met_auctionEnd[x, y, v10])
}

run transition__S07__a__S02__mediante_met_auctionEnd for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S06__mediante_met_auctionEnd for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S07__mediante_met_auctionEnd for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S09__mediante_met_auctionEnd for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S12__mediante_met_auctionEnd for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
pred transition__S07__a__S02__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS02[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S07__a__S06__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS06[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S07__a__S07__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS07[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S07__a__S09__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS09[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S07__a__S12__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS07[x] and partitionS12[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

run transition__S07__a__S02__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S06__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S07__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S09__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq
run transition__S07__a__S12__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Bidders, 10 SumatoriaSeq

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}


abstract sig AuctionState {}
one sig Deployed extends AuctionState{}
one sig Started extends AuctionState{}
one sig DepositPending extends AuctionState{} /* all slots sold, someone needs to call depositBids */
one sig Ended extends AuctionState{}
one sig Failed extends AuctionState{}

sig DepositLocker{}// concrete states
abstract sig EstadoConcreto {
	//Ownable
	_owner: Address,
	//DepositLocker
	_initialized: DepositLocker -> lone Bool,
	_deposited: DepositLocker-> lone Bool,
	_slasher: DepositLocker->lone Address,
	_depositorsProxy: DepositLocker-> lone Address,
	_releaseTimestamp: DepositLocker->lone Int,
	_canWithdraw: DepositLocker->(Address -> Bool),
	_numberOfDepositors: DepositLocker-> lone Int,
	_valuePerDepositor: DepositLocker-> lone Int,
	//ValidatorAuction
	_auctionDurationInDays: Int,
	_startPrice: Int,
	_minimalNumberOfParticipants: Int,
	_maximalNumberOfParticipants: Int,
	_auctionState: lone AuctionState,
	_depositLocker: DepositLocker,
	_whitelist: Address->lone Bool,
	_bids: Address -> lone Int,
	_bidders: seq Address,
	_startTime: Int,
	_closeTime: Int,
	_lowestSlotPrice: Int,
	_now: Int, //lo agrego para simular el paso del tiempo
	_init: Bool
}


pred invariante [e:EstadoConcreto] {
	e._init = True
	e._owner != Address0x0
	e._startPrice >= 0
	e._auctionDurationInDays >= 0
	e._minimalNumberOfParticipants > 0
	e._maximalNumberOfParticipants > 0
	e._minimalNumberOfParticipants <= e._maximalNumberOfParticipants
	e._startTime >= 0
	e._closeTime >= 0
	e._lowestSlotPrice > 0
	e._now >= 0
	e._depositLocker in e._initialized.Bool and  e._initialized[e._depositLocker] = True
	e._startTime.add[e._auctionDurationInDays] <= max and e._startTime.add[e._auctionDurationInDays]>=0
	e._now.add[e._auctionDurationInDays] <= max and e._now.add[e._auctionDurationInDays]>=0
	#Int.(e._bidders) = #(e._bids).Int
	all a:Address | a in (e._bids).Int implies a != Address0x0 and (e._bids[a] > 0  or (e._bids[a] = 0 and (e._auctionState = Ended or e._auctionState = Failed)))
	e._auctionState = DepositPending implies (all a:Address | a in (e._bids).Int implies e._bids[a] > 0) 
	all a:Address | a in (e._bids).Int iff a in Int.(e._bidders)
	all a:Address | a in e._whitelist.Bool implies e._whitelist[a] = True
	all a:Address | a in (e._bids).Int implies a in e._whitelist.Bool and e._whitelist[a] = True
	#(e._bids).Int = e._numberOfDepositors[e._depositLocker]
	e._auctionState = Ended iff e._deposited[e._depositLocker] = True
	Address0x0 !in DepositLocker.(e._depositorsProxy)
	e._depositLocker in e._valuePerDepositor.Int and e._valuePerDepositor[e._depositLocker] >= 0
	e._depositLocker in e._depositorsProxy.Address and some a:Address | e._depositorsProxy[e._depositLocker] = a
	e._auctionState = Ended implies e._valuePerDepositor[e._depositLocker] > 0
	e._valuePerDepositor[e._depositLocker] = 0 or e._valuePerDepositor[e._depositLocker] = e._lowestSlotPrice
	e._deposited[e._depositLocker] = True implies e._auctionState = Ended
	#Int.(e._bidders) = #e._bidders.Address
	e._lowestSlotPrice.mul[e._numberOfDepositors[e._depositLocker]] < max
	e._lowestSlotPrice.mul[e._numberOfDepositors[e._depositLocker]] >= 0
}


pred onlyOwner[e: EstadoConcreto, sender: Address] {
	sender = e._owner
}

pred isInitialised[e: EstadoConcreto] {
	e._initialized[e._depositLocker] = True
}

pred isDeposited[e: EstadoConcreto] {
	e._deposited[e._depositLocker] = True
}

pred isNotDeposited[e: EstadoConcreto] {
	e._deposited[e._depositLocker] = False
}

pred onlyDepositorsProxy[e: EstadoConcreto, sender: Address] {
	sender = e._depositorsProxy[e._depositLocker]
}

pred init[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, slasher: Address,
			depositorsProxy: Address, releaseTimestamp: Int] {
	//PRE
	onlyOwner[ein, sender]
	not isInitialised[ein]
	depositorsProxy != Address0x0
	releaseTimestamp > ein._now

	//POST
	// eout._releaseTimestamp[ein._depositLocker] = releaseTimestamp
	// eout._slasher[ein._depositLocker] = slasher
	// eout._depositorsProxy[ein._depositLocker] = depositorsProxy
	// eout._initialized[ein._depositLocker] = True
	eout._releaseTimestamp= ein._releaseTimestamp++ein._depositLocker->releaseTimestamp
	eout._slasher = ein._slasher++ein._depositLocker->slasher
	eout._depositorsProxy = ein._depositorsProxy++ein._depositLocker->depositorsProxy
	eout._initialized = ein._initialized++ein._depositLocker->True
	eout._valuePerDepositor = ein._depositLocker->0

	//Ownable
	// eout._owner = ein._owner
	//DepositLocker
	//eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	//eout._slasher = ein._slasher
	//eout._depositorsProxy = ein._depositorsProxy
	//eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	// eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now
}

pred registerDepositor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, depositor: Address] {
	//PRE
	isInitialised[ein]
	isNotDeposited[ein]
	onlyDepositorsProxy[ein, sender]
	ein._canWithdraw[ein._depositLocker][depositor] = False

	//POST
	// eout._canWithdraw[ein._depositLocker] = ein._canWithdraw[ein._depositLocker]++depositor->True
	eout._canWithdraw = ein._canWithdraw++ein._depositLocker->depositor->True
	eout._numberOfDepositors = ein._numberOfDepositors++ein._depositLocker->ein._numberOfDepositors[ein._depositLocker].add[1]

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	//eout._canWithdraw = ein._canWithdraw
	//eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now
}

pred deposit[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int, valuePerDepositor: Int] {
	//PRE
	isInitialised[ein]
	isNotDeposited[ein]
	onlyDepositorsProxy[ein, sender]
	ein._numberOfDepositors[ein._depositLocker] > 0
	valuePerDepositor > 0
	let depositAmount = ein._numberOfDepositors[ein._depositLocker].mul[valuePerDepositor] |
			// valuePerDepositor = depositAmount.div[ein._numberOfDepositors[ein._depositLocker]] and
			value = depositAmount

	//POST
	// eout._valuePerDepositor[ein._depositLocker] = valuePerDepositor
	eout._valuePerDepositor = ein._valuePerDepositor++ein._depositLocker->valuePerDepositor
	eout._deposited = ein._deposited++ein._depositLocker->True

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	//eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	//eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now
}

pred withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	isInitialised[ein]
	isDeposited[ein]
	ein._now >= ein._releaseTimestamp[ein._depositLocker]
	ein._canWithdraw[ein._depositLocker][sender] = True

	//POST
	// eout._canWithdraw[ein._depositLocker] = ein._canWithdraw[ein._depositLocker]++sender->False
	eout._canWithdraw = ein._canWithdraw++ein._depositLocker->(sender->False)

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	//eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now
}

pred slash[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, depositorToBeSlashed: Address] {
	//PRE
	isInitialised[ein]
	isDeposited[ein]
	sender = ein._slasher[ein._depositLocker]
	ein._canWithdraw[ein._depositLocker][depositorToBeSlashed] = True

	//POST
	eout._canWithdraw[ein._depositLocker] = ein._canWithdraw[ein._depositLocker]++depositorToBeSlashed->False
        //address(0).transfer(valuePerDepositor);

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	//eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._now = ein._now
}

/////////////////////////////////
/////ValidatorAuction
////////////////////////////////
pred stateIs[e: EstadoConcreto, state: AuctionState] {
	e._auctionState = state
}


pred pre_constructor[ein: EstadoConcreto] {
	ein._init = False
	no ein._auctionState
	ein._startPrice = 0
	ein._minimalNumberOfParticipants = 0
	ein._maximalNumberOfParticipants = 0
	ein._startTime = 0
	ein._closeTime = 0
	ein._lowestSlotPrice = 0
	ein._now = 0
}

pred pre_params_constructor[ein: EstadoConcreto, sender: Address, slasher: Address,	depositorsProxy: Address,
		startPriceInWei: Int, auctionDurationInDays: Int, minimalNumberOfParticipants: Int, maximalNumberOfParticipants: Int,
        releaseTimestamp: Int, depositLocker: DepositLocker] {
	auctionDurationInDays > 0
	//auctionDurationInDays < 100.mul[365] //En alloy no tiene sentido
	minimalNumberOfParticipants > 0
	maximalNumberOfParticipants > 0
	minimalNumberOfParticipants <= maximalNumberOfParticipants
	//startPriceInWei < 10.mul[30] //En alloy no tiene sentido
}


pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, slasher: Address,	depositorsProxy: Address,
		startPriceInWei: Int, auctionDurationInDays: Int, minimalNumberOfParticipants: Int, maximalNumberOfParticipants: Int,
        releaseTimestamp: Int, depositLocker: DepositLocker] {
	//PRE
	pre_constructor[ein]
	pre_params_constructor[ein, sender, slasher, depositorsProxy, startPriceInWei, auctionDurationInDays, minimalNumberOfParticipants, maximalNumberOfParticipants, releaseTimestamp, depositLocker]

	//POST
	eout._startPrice = startPriceInWei
	eout._auctionDurationInDays = auctionDurationInDays
	eout._maximalNumberOfParticipants = maximalNumberOfParticipants
	eout._minimalNumberOfParticipants = minimalNumberOfParticipants
	eout._depositLocker = depositLocker
	eout._auctionState = Deployed
	eout._init = True
	eout._lowestSlotPrice = 1

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	init[ein, eout, sender, slasher, depositorsProxy, releaseTimestamp]
	// eout._initialized = ein._initialized
	// eout._deposited = ein._deposited
	// eout._slasher = ein._slasher
	// eout._depositorsProxy = ein._depositorsProxy
	// eout._releaseTimestamp = ein._releaseTimestamp
	// eout._canWithdraw = ein._canWithdraw
	// eout._numberOfDepositors = ein._numberOfDepositors
	// eout._valuePerDepositor = ein._valuePerDepositor

	//ValidatorAuction
	//eout._auctionDurationInDays = ein._auctionDurationInDays
	//eout._startPrice = ein._startPrice
	//eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	//eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
	//eout._depositLocker = ein._depositLocker
	eout._whitelist = ein._whitelist
	eout._bids = ein._bids
	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	// eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now //lo agrego para simular el paso del tiempo
}

/*pred currentPrice[ein: EstadoConcreto, price: Int] {
	stateIs[ein, Started]
	ein._now >= ein._startTime
        
	let secondsSinceStart = ein._now.sub[ein._startTime] |
	priceAtElapsedTime[ein, secondsSinceStart, price]
}

pred priceAtElapsedTime[ein: EstadoConcreto, secondsSinceStart: Int, price: Int] {
        // To prevent overflows
	secondsSinceStart < 100.mul[365]
	let msSinceStart = 1000.mul[secondsSinceStart] | 
	     let relativeAuctionTime = msSinceStart.div[ein._auctionDurationInDays] |
        		let decayDivisor = 2 | //746571428571 | 
		     let decay = (relativeAuctionTime.mul[relativeAuctionTime].mul[relativeAuctionTime]).div[decayDivisor] |
        			 price = ein._startPrice.mul[1.add[relativeAuctionTime]].div[(1.add[relativeAuctionTime]).add[decay]]
        //return price;
}*/

pred pre_bid[e:EstadoConcreto] {
	stateIs[e, Started]
	e._now > e._startTime
	e._now <= e._startTime.add[e._auctionDurationInDays]
	e._init = True
}

pred pre_params_bid[ein: EstadoConcreto, sender: Address, value: Int, currentPrice: Int] {
	//(some p:Int | currentPrice[ein, p] and value >= p)
	currentPrice > 0
	value >= currentPrice
	ein._whitelist[sender] = True
	//!isSenderContract()
	#Int.(ein._bidders) < ein._maximalNumberOfParticipants
	sender !in (ein._bids).Int //ein._bids[sender] = 0
	sender = ein._depositorsProxy[ein._depositLocker] //Pre en registerDepositor
}

pred met_bid[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int, currentPrice: Int] {
	//PRE
	pre_bid[ein]
	pre_params_bid[ein, sender, value, currentPrice]

	//POST
	eout._bids = ein._bids++sender -> value
	eout._bidders = add[ein._bidders, sender]
	(//some p:Int | currentPrice[ein, p] and value >= p
		(currentPrice < ein._lowestSlotPrice) => eout._lowestSlotPrice = currentPrice
		else eout._lowestSlotPrice = ein._lowestSlotPrice
	)
	registerDepositor[ein, eout, sender, sender]
	
	(#eout._bidders = ein._maximalNumberOfParticipants) =>
		(eout._auctionState = DepositPending and eout._closeTime = ein._now)
	else
		(eout._auctionState = ein._auctionState and eout._closeTime = ein._closeTime)


	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	/*eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor*/
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
	eout._depositLocker = ein._depositLocker
	eout._whitelist = ein._whitelist
	//eout._bids = ein._bids
	//eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	//eout._closeTime = ein._closeTime
	//eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now
	eout._init = ein._init
}

pred pre_startAuction[e:EstadoConcreto] {
	stateIs[e, Deployed]
	e._initialized[e._depositLocker] = True
	e._init = True
}

pred pre_params_startAuction[ein: EstadoConcreto, sender: Address] {
	onlyOwner[ein, sender]
}

pred met_startAuction[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_startAuction[ein]
	pre_params_startAuction[ein, sender]

	//POST
	eout._auctionState = Started
	eout._startTime = ein._now

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
	eout._depositLocker = ein._depositLocker
	eout._whitelist = ein._whitelist
	eout._bids = ein._bids
	eout._bidders = ein._bidders
	//eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now
	eout._init = ein._init
}

pred pre_depositBids[e:EstadoConcreto] {
	stateIs[e, DepositPending]
	e._init = True
	isInitialised[e]
	isNotDeposited[e]
	e._numberOfDepositors[e._depositLocker] > 0
}

pred pre_params_depositBids[ein: EstadoConcreto, sender: Address, value: Int] {
	onlyDepositorsProxy[ein, sender]
	sender != Address0x0
	value = ein._lowestSlotPrice.mul[#ein._bidders]
}

pred met_depositBids[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int] {
	//PRE
	pre_depositBids[ein]
	pre_params_depositBids[ein, sender, value]

	//POST
	eout._auctionState = Ended
	//depositLocker.deposit.value(lowestSlotPrice * bidders.length)(lowestSlotPrice);
	deposit[ein, eout, sender, (ein._lowestSlotPrice.mul[#ein._bidders]), ein._lowestSlotPrice]
        
	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	/*eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor*/
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
	eout._depositLocker = ein._depositLocker
	eout._whitelist = ein._whitelist
	eout._bids = ein._bids
	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now
	eout._init = ein._init
}

pred pre_closeAuction[e:EstadoConcreto] {
	stateIs[e, Started]
	e._now > e._startTime.add[e._auctionDurationInDays]
	#e._bidders < e._maximalNumberOfParticipants
	e._init = True
}

pred pre_params_closeAuction[ein: EstadoConcreto, sender: Address] {

}

pred met_closeAuction[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_closeAuction[ein]
	pre_params_closeAuction[ein, sender]

	(#ein._bidders >= ein._minimalNumberOfParticipants) =>
		transitionToDepositPending[ein, eout]
	else
		transitionToAuctionFailed[ein, eout]

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	//eout._auctionState = ein._auctionState
	eout._depositLocker = ein._depositLocker
	eout._whitelist = ein._whitelist
	eout._bids = ein._bids
	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	//eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now
	eout._init = ein._init
}

pred pre_addToWhitelist[e:EstadoConcreto] {
	stateIs[e, Deployed]
	e._init = True
}

pred pre_params_addToWhitelist[ein: EstadoConcreto, sender: Address, addressesToWhitelist: Address] {
	onlyOwner[ein, sender]
}

pred met_addToWhitelist[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, addressesToWhitelist: Address] {
	//PRE
	pre_addToWhitelist[ein]
	pre_params_addToWhitelist[ein, sender, addressesToWhitelist]

	//POST
	eout._whitelist = ein._whitelist++addressesToWhitelist->True
	// (all a:Address| a in addressesToWhitelist.elems implies eout._whitelist[a] = True)
	// (all a:Address| a !in addressesToWhitelist.elems and a in (ein._whitelist.Bool)
	// 		implies eout._whitelist[a] = ein._whitelist[a])
	

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	eout._auctionState = ein._auctionState
	eout._depositLocker = ein._depositLocker
	//eout._whitelist = ein._whitelist
	eout._bids = ein._bids
	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now
	eout._init = ein._init
}

pred pre_withdraw[e:EstadoConcreto] {
	some a:Address | e._bids[a] > 0
	((e._auctionState = Ended and pre_withdrawAfterAuctionEnded[e] and
	some a:Address | e._bids[a] > e._lowestSlotPrice and
	e._bids[a].sub[e._lowestSlotPrice] <= e._bids[a])
	or (e._auctionState = Failed and stateIs[e, Failed]))
	e._init = True
}

pred pre_params_withdraw[ein: EstadoConcreto, sender: Address] {
	(ein._auctionState = Ended and  (ein._bids[sender] > ein._lowestSlotPrice and
	ein._bids[sender].sub[ein._lowestSlotPrice] <= ein._bids[sender])) or
	(ein._auctionState = Failed and (ein._bids[sender] > 0))
}

pred met_withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_withdraw[ein]
	pre_params_withdraw[ein, sender]
	
	//POST
	(ein._auctionState = Ended) =>
		withdrawAfterAuctionEnded[ein, eout,sender]
	else (ein._auctionState = Failed) =>
		withdrawAfterAuctionFailed[ein, eout,sender]

	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	eout._auctionState = ein._auctionState
	eout._depositLocker = ein._depositLocker
	eout._whitelist = ein._whitelist
	//eout._bids = ein._bids
	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	eout._now = ein._now
	eout._init = ein._init
}


pred withdrawAfterAuctionEnded[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_withdrawAfterAuctionEnded[ein]
	ein._bids[sender] > ein._lowestSlotPrice
	ein._bids[sender].sub[ein._lowestSlotPrice] <= ein._bids[sender]

	//POST
	eout._bids = ein._bids++sender->ein._lowestSlotPrice
}

pred pre_withdrawAfterAuctionEnded[e:EstadoConcreto] {
	stateIs[e, Ended]
}

pred withdrawAfterAuctionFailed[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	stateIs[ein, Failed]
	ein._bids[sender] > 0

	//POST
	//valueToWithdraw = bids[msg.sender];
	eout._bids = ein._bids++sender->0
	//msg.sender.transfer(valueToWithdraw);
}

pred pre_withdrawAfterAuctionFailed[e:EstadoConcreto] {
	stateIs[e, Failed]
}

pred transitionToDepositPending[ein: EstadoConcreto, eout: EstadoConcreto] {
	stateIs[ein, Started]

	eout._auctionState = DepositPending
	eout._closeTime = ein._now
}

pred transitionToAuctionFailed[ein: EstadoConcreto, eout: EstadoConcreto] {
	stateIs[ein, Started]

	eout._auctionState = Failed
	eout._closeTime = ein._now
}


pred pre_t[e:EstadoConcreto] {
	e._init = True
}

pred pre_params_t[ein: EstadoConcreto, sender:Address] {
	// timeElapsed > 0
}

pred met_t[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_t[ein]
	pre_params_t[ein, sender]
	
	//Ownable
	eout._owner = ein._owner
	//DepositLocker
	eout._initialized = ein._initialized
	eout._deposited = ein._deposited
	eout._slasher = ein._slasher
	eout._depositorsProxy = ein._depositorsProxy
	eout._releaseTimestamp = ein._releaseTimestamp
	eout._canWithdraw = ein._canWithdraw
	eout._numberOfDepositors = ein._numberOfDepositors
	eout._valuePerDepositor = ein._valuePerDepositor
	//ValidatorAuction
	eout._auctionDurationInDays = ein._auctionDurationInDays
	eout._startPrice = ein._startPrice
	eout._minimalNumberOfParticipants = ein._minimalNumberOfParticipants
	eout._maximalNumberOfParticipants = ein._maximalNumberOfParticipants
	eout._auctionState = ein._auctionState
	eout._depositLocker = ein._depositLocker
	eout._whitelist = ein._whitelist
	eout._bids = ein._bids
	eout._bidders = ein._bidders
	eout._startTime = ein._startTime
	eout._closeTime = ein._closeTime
	eout._lowestSlotPrice = ein._lowestSlotPrice
	// ein._now < max => eout._now = ein._now.add[timeElapsed] else eout._now = ein._now
	ein._now.add[ein._auctionDurationInDays] < max => eout._now = ein._now.add[1] else eout._now = ein._now
	eout._init = ein._init
}





//////////////////////////////////////////////////////////////////////////////////////
// I add a predicate for each possible theoretical partition //
//////////////////////////////////////////////////////////////////////////////////////
pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}



pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS09[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS10[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS11[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS12[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS13[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS14[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS15[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS16[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS17[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS18[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS19[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS20[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS21[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS22[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS23[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS24[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS25[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS26[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS27[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS28[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS29[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS30[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS31[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS32[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS33[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS34[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS35[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS36[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS37[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS38[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS39[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS40[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS41[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS42[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS43[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS44[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS45[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS46[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS47[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS48[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS49[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS50[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS51[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS52[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS53[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS54[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS55[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS56[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS57[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS58[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS59[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS60[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS61[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS62[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS63[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS64[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS65[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS66[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS67[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS68[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS69[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS70[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS71[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS72[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS73[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS74[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS75[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS76[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS77[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS78[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS79[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS80[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS81[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS82[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS83[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS84[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS85[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS86[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS87[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS88[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS89[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS90[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS91[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS92[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS93[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS94[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS95[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS96[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS97[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS98[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS99[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS100[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and pre_t[e]
}

pred partitionS101[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS102[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS103[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS104[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS105[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS106[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS107[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS108[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS109[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS110[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS111[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS112[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS113[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS114[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS115[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS116[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS117[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS118[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS119[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS120[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS121[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and pre_t[e]
}

pred partitionS122[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and pre_withdraw[e] and not pre_t[e]
}

pred partitionS123[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS124[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS125[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS126[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS127[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}

pred partitionS128[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_startAuction[e] and not pre_depositBids[e] and not pre_closeAuction[e] and not pre_addToWhitelist[e] and not pre_withdraw[e] and not pre_t[e]
}




//======predicates for blue queries======



pred blue_transition__S76__a__S76__mediante_met_t {
	some x: EstadoConcreto | partitionS76[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS76[y]))
}
run blue_transition__S76__a__S76__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S76__a__S121__mediante_met_startAuction {
	some x: EstadoConcreto | partitionS76[x] and (not pre_startAuction[x] or (all sender:{this/Address} | pre_params_startAuction[x,sender] implies some y:EstadoConcreto | met_startAuction[x,y,sender] and not partitionS121[y]))
}
run blue_transition__S76__a__S121__mediante_met_startAuction for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S106__a__S106__mediante_met_t {
	some x: EstadoConcreto | partitionS106[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS106[y]))
}
run blue_transition__S106__a__S106__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S115__a__S106__mediante_met_bid {
	some x: EstadoConcreto | partitionS115[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int}, currentPrice:{Int} | pre_params_bid[x,sender, value, currentPrice] implies some y:EstadoConcreto | met_bid[x,y,sender, value, currentPrice] and not partitionS106[y]))
}
run blue_transition__S115__a__S106__mediante_met_bid for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S115__a__S115__mediante_met_bid {
	some x: EstadoConcreto | partitionS115[x] and (not pre_bid[x] or (all sender:{this/Address}, value:{Int}, currentPrice:{Int} | pre_params_bid[x,sender, value, currentPrice] implies some y:EstadoConcreto | met_bid[x,y,sender, value, currentPrice] and not partitionS115[y]))
}
run blue_transition__S115__a__S115__mediante_met_bid for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S121__a__S103__mediante_met_t {
	some x: EstadoConcreto | partitionS121[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS103[y]))
}
run blue_transition__S121__a__S103__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S121__a__S115__mediante_met_t {
	some x: EstadoConcreto | partitionS121[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS115[y]))
}
run blue_transition__S121__a__S115__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S121__a__S121__mediante_met_t {
	some x: EstadoConcreto | partitionS121[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS121[y]))
}
run blue_transition__S121__a__S121__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S100__a__S100__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS100[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS100[y]))
}
run blue_transition__S100__a__S100__mediante_met_withdraw for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S100__a__S121__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS100[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS121[y]))
}
run blue_transition__S100__a__S121__mediante_met_withdraw for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S106__a__S100__mediante_met_depositBids {
	some x: EstadoConcreto | partitionS106[x] and (not pre_depositBids[x] or (all sender:{this/Address}, value:{Int} | pre_params_depositBids[x,sender, value] implies some y:EstadoConcreto | met_depositBids[x,y,sender, value] and not partitionS100[y]))
}
run blue_transition__S106__a__S100__mediante_met_depositBids for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S106__a__S121__mediante_met_depositBids {
	some x: EstadoConcreto | partitionS106[x] and (not pre_depositBids[x] or (all sender:{this/Address}, value:{Int} | pre_params_depositBids[x,sender, value] implies some y:EstadoConcreto | met_depositBids[x,y,sender, value] and not partitionS121[y]))
}
run blue_transition__S106__a__S121__mediante_met_depositBids for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S100__a__S100__mediante_met_t {
	some x: EstadoConcreto | partitionS100[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS100[y]))
}
run blue_transition__S100__a__S100__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S115__a__S103__mediante_met_t {
	some x: EstadoConcreto | partitionS115[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS103[y]))
}
run blue_transition__S115__a__S103__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S115__a__S115__mediante_met_t {
	some x: EstadoConcreto | partitionS115[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS115[y]))
}
run blue_transition__S115__a__S115__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S115__a__S121__mediante_met_t {
	some x: EstadoConcreto | partitionS115[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS121[y]))
}
run blue_transition__S115__a__S121__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S103__a__S100__mediante_met_closeAuction {
	some x: EstadoConcreto | partitionS103[x] and (not pre_closeAuction[x] or (all sender:{this/Address} | pre_params_closeAuction[x,sender] implies some y:EstadoConcreto | met_closeAuction[x,y,sender] and not partitionS100[y]))
}
run blue_transition__S103__a__S100__mediante_met_closeAuction for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S103__a__S106__mediante_met_closeAuction {
	some x: EstadoConcreto | partitionS103[x] and (not pre_closeAuction[x] or (all sender:{this/Address} | pre_params_closeAuction[x,sender] implies some y:EstadoConcreto | met_closeAuction[x,y,sender] and not partitionS106[y]))
}
run blue_transition__S103__a__S106__mediante_met_closeAuction for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S103__a__S121__mediante_met_closeAuction {
	some x: EstadoConcreto | partitionS103[x] and (not pre_closeAuction[x] or (all sender:{this/Address} | pre_params_closeAuction[x,sender] implies some y:EstadoConcreto | met_closeAuction[x,y,sender] and not partitionS121[y]))
}
run blue_transition__S103__a__S121__mediante_met_closeAuction for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S76__a__S76__mediante_met_addToWhitelist {
	some x: EstadoConcreto | partitionS76[x] and (not pre_addToWhitelist[x] or (all sender:{this/Address}, addressesToWhitelist:{this/Address} | pre_params_addToWhitelist[x,sender, addressesToWhitelist] implies some y:EstadoConcreto | met_addToWhitelist[x,y,sender, addressesToWhitelist] and not partitionS76[y]))
}
run blue_transition__S76__a__S76__mediante_met_addToWhitelist for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S103__a__S103__mediante_met_t {
	some x: EstadoConcreto | partitionS103[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS103[y]))
}
run blue_transition__S103__a__S103__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred blue_transition__S00__a__S76__mediante_met_constructor {
	some x: EstadoConcreto | partitionS00[x] and ((all sender:{this/Address}, slasher:{this/Address}, depositorsProxy:{this/Address}, startPriceInWei:{Int}, auctionDurationInDays:{Int}, minimalNumberOfParticipants:{Int}, maximalNumberOfParticipants:{Int}, releaseTimestamp:{Int}, depositLocker:{this/DepositLocker} | pre_params_constructor[x,sender, slasher, depositorsProxy, startPriceInWei, auctionDurationInDays, minimalNumberOfParticipants, maximalNumberOfParticipants, releaseTimestamp, depositLocker] implies some y:EstadoConcreto | met_constructor[x,y,sender, slasher, depositorsProxy, startPriceInWei, auctionDurationInDays, minimalNumberOfParticipants, maximalNumberOfParticipants, releaseTimestamp, depositLocker] and not partitionS76[y]))
}
run blue_transition__S00__a__S76__mediante_met_constructor for 10 EstadoConcreto, 3 DepositLocker




//======predicates for turquoise queries======



pred turquoise_transition__S106__a__S100_S121__mediante_met_depositBids {
	some x: EstadoConcreto | partitionS106[x] and (not pre_depositBids[x] or (all sender:{this/Address}, value:{Int} | pre_params_depositBids[x,sender, value] implies some y:EstadoConcreto | met_depositBids[x,y,sender, value] and not partitionS100[y] and not partitionS121[y]))
}
run turquoise_transition__S106__a__S100_S121__mediante_met_depositBids for 10 EstadoConcreto, 3 DepositLocker

pred turquoise_transition__S100__a__S100_S121__mediante_met_withdraw {
	some x: EstadoConcreto | partitionS100[x] and (not pre_withdraw[x] or (all sender:{this/Address} | pre_params_withdraw[x,sender] implies some y:EstadoConcreto | met_withdraw[x,y,sender] and not partitionS100[y] and not partitionS121[y]))
}
run turquoise_transition__S100__a__S100_S121__mediante_met_withdraw for 10 EstadoConcreto, 3 DepositLocker

pred turquoise_transition__S115__a__S103_S115_S121__mediante_met_t {
	some x: EstadoConcreto | partitionS115[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS103[y] and not partitionS115[y] and not partitionS121[y]))
}
run turquoise_transition__S115__a__S103_S115_S121__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred turquoise_transition__S121__a__S103_S115_S121__mediante_met_t {
	some x: EstadoConcreto | partitionS121[x] and (not pre_t[x] or (all sender:{this/Address} | pre_params_t[x,sender] implies some y:EstadoConcreto | met_t[x,y,sender] and not partitionS103[y] and not partitionS115[y] and not partitionS121[y]))
}
run turquoise_transition__S121__a__S103_S115_S121__mediante_met_t for 10 EstadoConcreto, 3 DepositLocker

pred turquoise_transition__S103__a__S100_S106_S121__mediante_met_closeAuction {
	some x: EstadoConcreto | partitionS103[x] and (not pre_closeAuction[x] or (all sender:{this/Address} | pre_params_closeAuction[x,sender] implies some y:EstadoConcreto | met_closeAuction[x,y,sender] and not partitionS100[y] and not partitionS106[y] and not partitionS121[y]))
}
run turquoise_transition__S103__a__S100_S106_S121__mediante_met_closeAuction for 10 EstadoConcreto, 3 DepositLocker


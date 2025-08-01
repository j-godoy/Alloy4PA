abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Address{balance: Int}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressBene0x7A29e extends Address{}

sig Deposit{d: Address->lone Int}// concrete states
abstract sig EstadoConcreto {
	_owner: Address,
	_admin: Address,
	_tokensRemaining: Int,
	_beneficiaryWallet: Address,
	_amountRaisedInWei: Int,
	_fundingMinCapInWei: Int,
	_currentStatus: lone State,
	_fundingStartBlock: Int,
	_fundingEndBlock: Int,
	_isCrowdSaleClosed: Bool,
	_areFundsReleasedToBeneficiary: Bool,
	_isCrowdSaleSetup: Bool,
	_usersEPXfundValue: Deposit,
	_balance: Int,
	_blockNumber: Int, //lo agrego para simular el paso del tiempo
	_init: Bool
}

abstract sig State{}
one sig CrowdsaleDeployedToChain extends State {}
one sig CrowdsaleIsSetup extends State{}
one sig InProgress_Eth_low_Softcap extends State{}
one sig InProgress_Eth_ge_Softcap extends State{}
one sig Unsuccessful_Eth_low_Softcap extends State{}
one sig Successful_EPX_ge_Hardcap extends State{}
one sig Successful_Eth_ge_Softcap extends State{}


fun LIMIT[]: Int {3}


pred invariante [e:EstadoConcreto] {
	e._init = True
	e._admin != Address0x0
	e._owner != Address0x0
	e._admin = e._owner
	
	no e._currentStatus iff e._admin = Address0x0
	
	/*
	e._currentStatus = InProgress_Eth_low_Softcap implies
		((e._amountRaisedInWei < e._fundingMinCapInWei) and (e._blockNumber <= e._fundingEndBlock and e._blockNumber >= e._fundingStartBlock))
		
	e._currentStatus = Unsuccessful_Eth_low_Softcap implies 
	((e._amountRaisedInWei < e._fundingMinCapInWei) and (e._blockNumber > e._fundingEndBlock))
	
	e._currentStatus = Successful_EPX_ge_Hardcap implies
		((e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._tokensRemaining = 0))
		
	e._currentStatus = Successful_Eth_ge_Softcap implies 
		((e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._blockNumber > e._fundingEndBlock) and (e._tokensRemaining > 0))
		
	e._currentStatus = InProgress_Eth_ge_Softcap implies
		((e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._tokensRemaining > 0) and (e._blockNumber <= e._fundingEndBlock))
		*/

	e._isCrowdSaleSetup = False implies e._currentStatus = CrowdsaleDeployedToChain
	e._isCrowdSaleClosed = True implies e._currentStatus != CrowdsaleDeployedToChain

	e._isCrowdSaleClosed = True implies
	(
			not ((e._amountRaisedInWei < e._fundingMinCapInWei) and (e._blockNumber <= e._fundingEndBlock && e._blockNumber >= e._fundingStartBlock))
			and not ((e._amountRaisedInWei < e._fundingMinCapInWei) and (e._blockNumber < e._fundingStartBlock))
			and (
				(((e._amountRaisedInWei < e._fundingMinCapInWei) and (e._blockNumber > e._fundingEndBlock)) or 
				(e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._tokensRemaining = 0) or
				((e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._blockNumber > e._fundingEndBlock) and (e._tokensRemaining > 0)))
			)
	)
		
	
	((e._tokensRemaining > 0 or e._fundingStartBlock > 0 or e._fundingEndBlock > 0 or e._fundingMinCapInWei > 0)
		implies e._currentStatus != CrowdsaleDeployedToChain)
	e._areFundsReleasedToBeneficiary = True implies e._isCrowdSaleSetup = True

	//No Negativos
	e._blockNumber >=0 and e._fundingEndBlock >=0 and e._fundingStartBlock >= 0
	e._balance >= 0 and e._blockNumber >= 0 and e._amountRaisedInWei >=0
	e._fundingStartBlock < max.sub[2]
	e._tokensRemaining >= 0
	e._fundingMinCapInWei >=0
	//sumatoria[e._usersEPXfundValue, e._amountRaisedInWei]

	//fixed size: Int= 0,1,2,3; max length=4
	all d0:Address | e._usersEPXfundValue.d[d0] >= 0 and e._usersEPXfundValue.d[d0] <= LIMIT[]
	#(e._usersEPXfundValue.d.Int) <= 4
}

// fun sumof[s:seq Int]: Int {
// 	s=none->none implies 0
// 	else s=0->0 implies 0
// 	else s=0->1 implies 1
// 	else s=0->2 implies 2
// 	else s=0->3 implies 3
// 	else s=0->4 implies 4
// 	else s=0->5 implies 5
// 	else s=0->0+1->0 implies 0
// 	else s=0->0+1->1 implies 1
// 	else s=0->0+1->2 implies 2
// 	else s=0->0+1->3 implies 3
// 	else s=0->0+1->4 implies 4
// 	else s=0->0+1->5 implies 5
// 	else s=0->1+1->0 implies 1
// 	else s=0->1+1->1 implies 2
// 	else s=0->1+1->2 implies 3
// 	else s=0->1+1->3 implies 4
// 	else s=0->1+1->4 implies 5
// 	else s=0->1+1->5 implies 6
// 	else s=0->2+1->0 implies 2
// 	else s=0->2+1->1 implies 3
// 	else s=0->2+1->2 implies 4
// 	else s=0->2+1->3 implies 5
// 	else s=0->2+1->4 implies 6
// 	else s=0->2+1->5 implies 7
// 	else s=0->3+1->0 implies 3
// 	else s=0->3+1->1 implies 4
// 	else s=0->3+1->2 implies 5
// 	else s=0->3+1->3 implies 6
// 	else s=0->3+1->4 implies 7
// 	else s=0->3+1->5 implies 8
// 	else s=0->4+1->0 implies 4
// 	else s=0->4+1->1 implies 5
// 	else s=0->4+1->2 implies 6
// 	else s=0->4+1->3 implies 7
// 	else s=0->4+1->4 implies 8
// 	else s=0->4+1->5 implies 9
// 	else s=0->5+1->0 implies 5
// 	else s=0->5+1->1 implies 6
// 	else s=0->5+1->2 implies 7
// 	else s=0->5+1->3 implies 8
// 	else s=0->5+1->4 implies 9
// 	else s=0->5+1->5 implies 10
// 	else s=0->0+1->0+2->0 implies 0
// 	else s=0->0+1->0+2->1 implies 1
// 	else s=0->0+1->0+2->2 implies 2
// 	else s=0->0+1->0+2->3 implies 3
// 	else s=0->0+1->0+2->4 implies 4
// 	else s=0->0+1->0+2->5 implies 5
// 	else s=0->0+1->1+2->0 implies 1
// 	else s=0->0+1->1+2->1 implies 2
// 	else s=0->0+1->1+2->2 implies 3
// 	else s=0->0+1->1+2->3 implies 4
// 	else s=0->0+1->1+2->4 implies 5
// 	else s=0->0+1->1+2->5 implies 6
// 	else s=0->0+1->2+2->0 implies 2
// 	else s=0->0+1->2+2->1 implies 3
// 	else s=0->0+1->2+2->2 implies 4
// 	else s=0->0+1->2+2->3 implies 5
// 	else s=0->0+1->2+2->4 implies 6
// 	else s=0->0+1->2+2->5 implies 7
// 	else s=0->0+1->3+2->0 implies 3
// 	else s=0->0+1->3+2->1 implies 4
// 	else s=0->0+1->3+2->2 implies 5
// 	else s=0->0+1->3+2->3 implies 6
// 	else s=0->0+1->3+2->4 implies 7
// 	else s=0->0+1->3+2->5 implies 8
// 	else s=0->0+1->4+2->0 implies 4
// 	else s=0->0+1->4+2->1 implies 5
// 	else s=0->0+1->4+2->2 implies 6
// 	else s=0->0+1->4+2->3 implies 7
// 	else s=0->0+1->4+2->4 implies 8
// 	else s=0->0+1->4+2->5 implies 9
// 	else s=0->0+1->5+2->0 implies 5
// 	else s=0->0+1->5+2->1 implies 6
// 	else s=0->0+1->5+2->2 implies 7
// 	else s=0->0+1->5+2->3 implies 8
// 	else s=0->0+1->5+2->4 implies 9
// 	else s=0->0+1->5+2->5 implies 10
// 	else s=0->1+1->0+2->0 implies 1
// 	else s=0->1+1->0+2->1 implies 2
// 	else s=0->1+1->0+2->2 implies 3
// 	else s=0->1+1->0+2->3 implies 4
// 	else s=0->1+1->0+2->4 implies 5
// 	else s=0->1+1->0+2->5 implies 6
// 	else s=0->1+1->1+2->0 implies 2
// 	else s=0->1+1->1+2->1 implies 3
// 	else s=0->1+1->1+2->2 implies 4
// 	else s=0->1+1->1+2->3 implies 5
// 	else s=0->1+1->1+2->4 implies 6
// 	else s=0->1+1->1+2->5 implies 7
// 	else s=0->1+1->2+2->0 implies 3
// 	else s=0->1+1->2+2->1 implies 4
// 	else s=0->1+1->2+2->2 implies 5
// 	else s=0->1+1->2+2->3 implies 6
// 	else s=0->1+1->2+2->4 implies 7
// 	else s=0->1+1->2+2->5 implies 8
// 	else s=0->1+1->3+2->0 implies 4
// 	else s=0->1+1->3+2->1 implies 5
// 	else s=0->1+1->3+2->2 implies 6
// 	else s=0->1+1->3+2->3 implies 7
// 	else s=0->1+1->3+2->4 implies 8
// 	else s=0->1+1->3+2->5 implies 9
// 	else s=0->1+1->4+2->0 implies 5
// 	else s=0->1+1->4+2->1 implies 6
// 	else s=0->1+1->4+2->2 implies 7
// 	else s=0->1+1->4+2->3 implies 8
// 	else s=0->1+1->4+2->4 implies 9
// 	else s=0->1+1->4+2->5 implies 10
// 	else s=0->1+1->5+2->0 implies 6
// 	else s=0->1+1->5+2->1 implies 7
// 	else s=0->1+1->5+2->2 implies 8
// 	else s=0->1+1->5+2->3 implies 9
// 	else s=0->1+1->5+2->4 implies 10
// 	else s=0->1+1->5+2->5 implies 11
// 	else s=0->2+1->0+2->0 implies 2
// 	else s=0->2+1->0+2->1 implies 3
// 	else s=0->2+1->0+2->2 implies 4
// 	else s=0->2+1->0+2->3 implies 5
// 	else s=0->2+1->0+2->4 implies 6
// 	else s=0->2+1->0+2->5 implies 7
// 	else s=0->2+1->1+2->0 implies 3
// 	else s=0->2+1->1+2->1 implies 4
// 	else s=0->2+1->1+2->2 implies 5
// 	else s=0->2+1->1+2->3 implies 6
// 	else s=0->2+1->1+2->4 implies 7
// 	else s=0->2+1->1+2->5 implies 8
// 	else s=0->2+1->2+2->0 implies 4
// 	else s=0->2+1->2+2->1 implies 5
// 	else s=0->2+1->2+2->2 implies 6
// 	else s=0->2+1->2+2->3 implies 7
// 	else s=0->2+1->2+2->4 implies 8
// 	else s=0->2+1->2+2->5 implies 9
// 	else s=0->2+1->3+2->0 implies 5
// 	else s=0->2+1->3+2->1 implies 6
// 	else s=0->2+1->3+2->2 implies 7
// 	else s=0->2+1->3+2->3 implies 8
// 	else s=0->2+1->3+2->4 implies 9
// 	else s=0->2+1->3+2->5 implies 10
// 	else s=0->2+1->4+2->0 implies 6
// 	else s=0->2+1->4+2->1 implies 7
// 	else s=0->2+1->4+2->2 implies 8
// 	else s=0->2+1->4+2->3 implies 9
// 	else s=0->2+1->4+2->4 implies 10
// 	else s=0->2+1->4+2->5 implies 11
// 	else s=0->2+1->5+2->0 implies 7
// 	else s=0->2+1->5+2->1 implies 8
// 	else s=0->2+1->5+2->2 implies 9
// 	else s=0->2+1->5+2->3 implies 10
// 	else s=0->2+1->5+2->4 implies 11
// 	else s=0->2+1->5+2->5 implies 12
// 	else s=0->3+1->0+2->0 implies 3
// 	else s=0->3+1->0+2->1 implies 4
// 	else s=0->3+1->0+2->2 implies 5
// 	else s=0->3+1->0+2->3 implies 6
// 	else s=0->3+1->0+2->4 implies 7
// 	else s=0->3+1->0+2->5 implies 8
// 	else s=0->3+1->1+2->0 implies 4
// 	else s=0->3+1->1+2->1 implies 5
// 	else s=0->3+1->1+2->2 implies 6
// 	else s=0->3+1->1+2->3 implies 7
// 	else s=0->3+1->1+2->4 implies 8
// 	else s=0->3+1->1+2->5 implies 9
// 	else s=0->3+1->2+2->0 implies 5
// 	else s=0->3+1->2+2->1 implies 6
// 	else s=0->3+1->2+2->2 implies 7
// 	else s=0->3+1->2+2->3 implies 8
// 	else s=0->3+1->2+2->4 implies 9
// 	else s=0->3+1->2+2->5 implies 10
// 	else s=0->3+1->3+2->0 implies 6
// 	else s=0->3+1->3+2->1 implies 7
// 	else s=0->3+1->3+2->2 implies 8
// 	else s=0->3+1->3+2->3 implies 9
// 	else s=0->3+1->3+2->4 implies 10
// 	else s=0->3+1->3+2->5 implies 11
// 	else s=0->3+1->4+2->0 implies 7
// 	else s=0->3+1->4+2->1 implies 8
// 	else s=0->3+1->4+2->2 implies 9
// 	else s=0->3+1->4+2->3 implies 10
// 	else s=0->3+1->4+2->4 implies 11
// 	else s=0->3+1->4+2->5 implies 12
// 	else s=0->3+1->5+2->0 implies 8
// 	else s=0->3+1->5+2->1 implies 9
// 	else s=0->3+1->5+2->2 implies 10
// 	else s=0->3+1->5+2->3 implies 11
// 	else s=0->3+1->5+2->4 implies 12
// 	else s=0->3+1->5+2->5 implies 13
// 	else s=0->4+1->0+2->0 implies 4
// 	else s=0->4+1->0+2->1 implies 5
// 	else s=0->4+1->0+2->2 implies 6
// 	else s=0->4+1->0+2->3 implies 7
// 	else s=0->4+1->0+2->4 implies 8
// 	else s=0->4+1->0+2->5 implies 9
// 	else s=0->4+1->1+2->0 implies 5
// 	else s=0->4+1->1+2->1 implies 6
// 	else s=0->4+1->1+2->2 implies 7
// 	else s=0->4+1->1+2->3 implies 8
// 	else s=0->4+1->1+2->4 implies 9
// 	else s=0->4+1->1+2->5 implies 10
// 	else s=0->4+1->2+2->0 implies 6
// 	else s=0->4+1->2+2->1 implies 7
// 	else s=0->4+1->2+2->2 implies 8
// 	else s=0->4+1->2+2->3 implies 9
// 	else s=0->4+1->2+2->4 implies 10
// 	else s=0->4+1->2+2->5 implies 11
// 	else s=0->4+1->3+2->0 implies 7
// 	else s=0->4+1->3+2->1 implies 8
// 	else s=0->4+1->3+2->2 implies 9
// 	else s=0->4+1->3+2->3 implies 10
// 	else s=0->4+1->3+2->4 implies 11
// 	else s=0->4+1->3+2->5 implies 12
// 	else s=0->4+1->4+2->0 implies 8
// 	else s=0->4+1->4+2->1 implies 9
// 	else s=0->4+1->4+2->2 implies 10
// 	else s=0->4+1->4+2->3 implies 11
// 	else s=0->4+1->4+2->4 implies 12
// 	else s=0->4+1->4+2->5 implies 13
// 	else s=0->4+1->5+2->0 implies 9
// 	else s=0->4+1->5+2->1 implies 10
// 	else s=0->4+1->5+2->2 implies 11
// 	else s=0->4+1->5+2->3 implies 12
// 	else s=0->4+1->5+2->4 implies 13
// 	else s=0->4+1->5+2->5 implies 14
// 	else s=0->5+1->0+2->0 implies 5
// 	else s=0->5+1->0+2->1 implies 6
// 	else s=0->5+1->0+2->2 implies 7
// 	else s=0->5+1->0+2->3 implies 8
// 	else s=0->5+1->0+2->4 implies 9
// 	else s=0->5+1->0+2->5 implies 10
// 	else s=0->5+1->1+2->0 implies 6
// 	else s=0->5+1->1+2->1 implies 7
// 	else s=0->5+1->1+2->2 implies 8
// 	else s=0->5+1->1+2->3 implies 9
// 	else s=0->5+1->1+2->4 implies 10
// 	else s=0->5+1->1+2->5 implies 11
// 	else s=0->5+1->2+2->0 implies 7
// 	else s=0->5+1->2+2->1 implies 8
// 	else s=0->5+1->2+2->2 implies 9
// 	else s=0->5+1->2+2->3 implies 10
// 	else s=0->5+1->2+2->4 implies 11
// 	else s=0->5+1->2+2->5 implies 12
// 	else s=0->5+1->3+2->0 implies 8
// 	else s=0->5+1->3+2->1 implies 9
// 	else s=0->5+1->3+2->2 implies 10
// 	else s=0->5+1->3+2->3 implies 11
// 	else s=0->5+1->3+2->4 implies 12
// 	else s=0->5+1->3+2->5 implies 13
// 	else s=0->5+1->4+2->0 implies 9
// 	else s=0->5+1->4+2->1 implies 10
// 	else s=0->5+1->4+2->2 implies 11
// 	else s=0->5+1->4+2->3 implies 12
// 	else s=0->5+1->4+2->4 implies 13
// 	else s=0->5+1->4+2->5 implies 14
// 	else s=0->5+1->5+2->0 implies 10
// 	else s=0->5+1->5+2->1 implies 11
// 	else s=0->5+1->5+2->2 implies 12
// 	else s=0->5+1->5+2->3 implies 13
// 	else s=0->5+1->5+2->4 implies 14
// 	else s=0->5+1->5+2->5 implies 15
// 	else 0
// }

// pred sumatoria [s: set Deposit, suma: Int] {
// 	some sumaSeq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
// }

// pred sumatoriaSubSeq [s: set Deposit, suma: Int] {
// 	some sumaSeq: SumatoriaSeq, subseq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and
// 			subSeq[sumaSeq.sec, subseq.sec] and sumof[subseq.sec] = suma
// }

// pred subSeq [original: seq Int, subseq: seq Int] {
// 	#subseq <= #original
// 	all i: Int | some subseq[i] implies subseq[i] in original.elems
// 	all i: Int | some subseq[i] implies #subseq.i <= #original.i
// }

// pred toSeq [s: set Deposit, ret: seq Int] {
// 	all d0: s.d.Int | some i: Int | ret[i]=s.d[d0] //Todo elemento del set está en la seq
// 	all i: Int | some ret[i] implies some d0: s.d.Int | s.d[d0]=ret[i]//Todo elemento de la seq está en el set
// 	all i: Int | #(s.d.i) = #(ret.i) //#elem(set,e) = #elem(seq,e)
// 	#(s.d.Int)=#(ret)
// }

// sig SumatoriaSeq {sec: seq Int}

pred pre_constructor[e: EstadoConcreto] {
	e._init = False
	e._owner = Address0x0
	e._admin = Address0x0
	e._tokensRemaining = 0
	e._beneficiaryWallet = Address0x0
	e._amountRaisedInWei = 0
	e._fundingMinCapInWei = 0
	no e._currentStatus
	e._fundingStartBlock = 0
	e._fundingEndBlock = 0
	e._isCrowdSaleClosed = False
	e._areFundsReleasedToBeneficiary = False
	e._isCrowdSaleSetup = False
	#e._usersEPXfundValue.d = 0
	e._balance = 0
	e._blockNumber >=0
}

pred pre_params_constructor [ein: EstadoConcreto, sender:Address] {
	sender != Address0x0
}

pred met_constructor [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender]

	//Post
	eout._owner = sender
	eout._admin = sender
	eout._currentStatus = CrowdsaleDeployedToChain
	eout._init = True

	//eout._owner = ein._owner
	//eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	//eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}


pred pre_setupCrowdsale[e: EstadoConcreto] {
	e._isCrowdSaleSetup = False
	e._beneficiaryWallet = Address0x0
	e._init = True
}

pred pre_params_setupCrowdsale[ein: EstadoConcreto, sender:Address, fundingStartBlock: Int, fundingEndBlock: Int, value: Int] {
	ein._owner = sender
	ein._admin = sender
	fundingStartBlock >=0 and fundingEndBlock>=0
}

pred met_setupCrowdsale[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
	fundingStartBlock: Int, fundingEndBlock: Int, value: Int] {
	//PRE
	pre_setupCrowdsale [ein]
	pre_params_setupCrowdsale[ein, sender, fundingStartBlock, fundingEndBlock, value]
		
	//POST
	eout._beneficiaryWallet = AddressBene0x7A29e
	eout._fundingMinCapInWei = 3
	eout._amountRaisedInWei = 0
	eout._tokensRemaining = 6
	eout._fundingStartBlock = fundingStartBlock
	eout._fundingEndBlock = fundingEndBlock
	eout._isCrowdSaleSetup = True
	eout._isCrowdSaleClosed = False
	eout._currentStatus = CrowdsaleIsSetup

	eout._owner = ein._owner
	eout._admin = ein._admin
	//eout._tokensRemaining = ein._tokensRemaining
	//eout._beneficiaryWallet = ein._beneficiaryWallet
	//eout._amountRaisedInWei = ein._amountRaisedInWei
	//eout._fundingMinCapInWei = ein._fundingMinCapInWei
	//eout._currentStatus = ein._currentStatus
	//eout._fundingStartBlock = ein._fundingStartBlock
	//eout._fundingEndBlock = ein._fundingEndBlock
	//eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	//eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
}

/*
pred pre_setupCrowdsaleRetNotAuthorised[e: EstadoConcreto] {
	not pre_setupCrowdsale[e]
}

pred setupCrowdsaleRetNotAuthorised[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
	fundingStartBlock: Int, fundingEndBlock: Int, value: Int] {
	//PRE
	pre_setupCrowdsaleRetNotAuthorised[ein]
	ein._owner = sender // porque hay un modifier
	ein._admin != sender
	timeElapsed >= 0

	//POST

	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}
*/

/*
pred pre_setupCrowdsaleCampCantChange[e: EstadoConcreto] {
	not pre_setupCrowdsale[e]
}

pred setupCrowdsaleCampCantChange[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
	fundingStartBlock: Int, fundingEndBlock: Int, value: Int] {
	//PRE
	pre_setupCrowdsaleCampCantChange[ein]
	ein._owner = sender
	ein._admin = sender
	timeElapsed >= 0

	//POST

	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}
*/

fun checkPrice[e:EstadoConcreto]: Int {
	//e._blockNumber >= fundingStartBlock+177534 implies 7600
    	//e._block.number >= fundingStartBlock+124274 implies 8200
	//e._block.number >= fundingStartBlock implies 8800
	
	e._blockNumber >= e._fundingStartBlock.add[2] implies 1
	else e._blockNumber >= e._fundingStartBlock.add[1] implies 2
	else e._blockNumber >= e._fundingStartBlock implies 3
	else 0
}



pred pre_buy[e: EstadoConcreto] {
	e._blockNumber <= e._fundingEndBlock
	e._blockNumber >= e._fundingStartBlock
	e._tokensRemaining > 0
	e._init = True
}

pred pre_params_buy[ein: EstadoConcreto, sender:Address, value:Int] {
	value >= 0 //dejo >=0 en lugar de > 0 para evitar problema de llegar al entero maximo
	sender != Address0x0
	ein._usersEPXfundValue.d[sender].add[value] <= LIMIT[]
	ein._amountRaisedInWei.add[value] <= max
	ein._amountRaisedInWei.add[value] >= 0
	value.add[checkPrice[ein]] <= max
	value.add[checkPrice[ein]] >= 0
	ein._tokensRemaining.sub[value.add[checkPrice[ein]]] >= 0
}

pred met_buy[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value:Int] {
	//PRE
	pre_buy[ein]
	pre_params_buy[ein, sender, value]
	
	//POST
	ein._amountRaisedInWei < max => {eout._amountRaisedInWei = ein._amountRaisedInWei.add[value]}
	else {eout._amountRaisedInWei = ein._amountRaisedInWei}
	
	eout._usersEPXfundValue.d = ein._usersEPXfundValue.d++sender->ein._usersEPXfundValue.d[sender].add[value]
	//let rewardTransferAmount = (value.mul[checkPrice[ein]).div[100000000000000] |
	
	//let rewardTransferAmount = value.mul[checkPrice[ein]] |
	let rewardTransferAmount = value.add[checkPrice[ein]] |
		eout._tokensRemaining = ein._tokensRemaining.sub[rewardTransferAmount]
		//tokenReward.transfer(msg.sender, rewardTransferAmount);
		
	
	eout._owner = ein._owner
	eout._admin = ein._admin
	//eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	//eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	//eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
}



pred pre_checkGoalReached[e: EstadoConcreto] {
	e._isCrowdSaleSetup = True
	e._init = True
}

pred pre_params_checkGoalReached[ein: EstadoConcreto, sender:Address] {
	ein._owner = sender
}

pred met_checkGoalReached[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_checkGoalReached[ein]
	pre_params_checkGoalReached[ein, sender]
	
	
	//POST
	(ein._amountRaisedInWei < ein._fundingMinCapInWei and ein._blockNumber <= ein._fundingEndBlock
	and ein._blockNumber >= ein._fundingStartBlock) // ICO in progress, under softcap
		=> (eout._areFundsReleasedToBeneficiary = False and eout._isCrowdSaleClosed = False
			and eout._currentStatus = InProgress_Eth_low_Softcap)
	else (ein._amountRaisedInWei < ein._fundingMinCapInWei and ein._blockNumber < ein._fundingStartBlock) // ICO has not started
     		=> (eout._areFundsReleasedToBeneficiary = False and eout._isCrowdSaleClosed = False
			and eout._currentStatus = CrowdsaleIsSetup)
	else (ein._amountRaisedInWei < ein._fundingMinCapInWei and ein._blockNumber > ein._fundingEndBlock) // ICO ended, under softcap
		=> eout._areFundsReleasedToBeneficiary = False and eout._isCrowdSaleClosed = True
			and eout._currentStatus = Unsuccessful_Eth_low_Softcap
	else (ein._amountRaisedInWei >= ein._fundingMinCapInWei and ein._tokensRemaining = 0) // ICO ended, all tokens bought!
		=> (eout._areFundsReleasedToBeneficiary = True and eout._isCrowdSaleClosed = True
			and eout._currentStatus = Successful_EPX_ge_Hardcap)
	else (ein._amountRaisedInWei >= ein._fundingMinCapInWei and ein._blockNumber > ein._fundingEndBlock
	and ein._tokensRemaining > 0) // ICO ended, over softcap!
		=> (eout._areFundsReleasedToBeneficiary = True and eout._isCrowdSaleClosed = True
			and eout._currentStatus = Successful_Eth_ge_Softcap)
	else (ein._amountRaisedInWei >= ein._fundingMinCapInWei and ein._tokensRemaining > 0
	and ein._blockNumber <= ein._fundingEndBlock) // ICO in progress, over softcap!
		=> (eout._areFundsReleasedToBeneficiary = True and eout._isCrowdSaleClosed = False
			and eout._currentStatus = InProgress_Eth_ge_Softcap)
	else eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
		and eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
		and eout._currentStatus = ein._currentStatus

	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	//eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	//eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	//eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
}


pred pre_refund[e: EstadoConcreto] {
	e._amountRaisedInWei < e._fundingMinCapInWei
	e._isCrowdSaleClosed = True
	e._blockNumber > e._fundingEndBlock
	some a:Address | e._usersEPXfundValue.d[a] > 0
	e._init = True
}

pred pre_params_refund[ein: EstadoConcreto, sender:Address] {
	ein._usersEPXfundValue.d[sender] > 0
}

pred met_refund[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_refund[ein]
	pre_params_refund[ein, sender]	
	
	//POST
	eout._usersEPXfundValue.d = ein._usersEPXfundValue.d++sender->0

	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	//eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
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
	
	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	// eout._blockNumber = ein._blockNumber.add[timeElapsed]
	ein._blockNumber < max => eout._blockNumber = ein._blockNumber.add[1] else eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
}


//////////////////////////////////////////////////////////////////////////////////////
// I add a predicate for each possible theoretical partition //
//////////////////////////////////////////////////////////////////////////////////////

pred partitionS00[e: EstadoConcreto]{
	(pre_constructor[e])
}


pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS09[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS10[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS11[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS12[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS13[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS14[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS15[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS16[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS17[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS18[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS19[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS20[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS21[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS22[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS23[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS24[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS25[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS26[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS27[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS28[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS29[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS30[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS31[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS32[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS33[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS34[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS35[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS36[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS37[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS38[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS39[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS40[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS41[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS42[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS43[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and pre_t[e]
}

pred partitionS44[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS45[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS46[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS47[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS48[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS49[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS50[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS51[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS52[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS53[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS54[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS55[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS56[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS57[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS58[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and pre_t[e]
}

pred partitionS59[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and pre_refund[e] and not pre_t[e]
}

pred partitionS60[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS61[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS62[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS63[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}

pred partitionS64[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_setupCrowdsale[e] and not pre_buy[e] and not pre_checkGoalReached[e] and not pre_refund[e] and not pre_t[e]
}




pred transition__S23__a__S23__mediante_met_setupCrowdsale{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int, v22:Int |
		partitionS23[x] and partitionS23[y] and
		v10 != Address0x0 and met_setupCrowdsale[x, y, v10, v20, v21, v22])
}

pred transition__S23__a__S25__mediante_met_setupCrowdsale{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int, v22:Int |
		partitionS23[x] and partitionS25[y] and
		v10 != Address0x0 and met_setupCrowdsale[x, y, v10, v20, v21, v22])
}

pred transition__S23__a__S44__mediante_met_setupCrowdsale{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int, v22:Int |
		partitionS23[x] and partitionS44[y] and
		v10 != Address0x0 and met_setupCrowdsale[x, y, v10, v20, v21, v22])
}

pred transition__S23__a__S49__mediante_met_setupCrowdsale{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int, v22:Int |
		partitionS23[x] and partitionS49[y] and
		v10 != Address0x0 and met_setupCrowdsale[x, y, v10, v20, v21, v22])
}

pred transition__S23__a__S58__mediante_met_setupCrowdsale{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int, v22:Int |
		partitionS23[x] and partitionS58[y] and
		v10 != Address0x0 and met_setupCrowdsale[x, y, v10, v20, v21, v22])
}

run transition__S23__a__S23__mediante_met_setupCrowdsale for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S25__mediante_met_setupCrowdsale for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S44__mediante_met_setupCrowdsale for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S49__mediante_met_setupCrowdsale for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S58__mediante_met_setupCrowdsale for 10 EstadoConcreto, 3 Deposit
pred transition__S23__a__S23__mediante_met_buy{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS23[x] and partitionS23[y] and
		v10 != Address0x0 and met_buy[x, y, v10, v20])
}

pred transition__S23__a__S25__mediante_met_buy{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS23[x] and partitionS25[y] and
		v10 != Address0x0 and met_buy[x, y, v10, v20])
}

pred transition__S23__a__S44__mediante_met_buy{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS23[x] and partitionS44[y] and
		v10 != Address0x0 and met_buy[x, y, v10, v20])
}

pred transition__S23__a__S49__mediante_met_buy{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS23[x] and partitionS49[y] and
		v10 != Address0x0 and met_buy[x, y, v10, v20])
}

pred transition__S23__a__S58__mediante_met_buy{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS23[x] and partitionS58[y] and
		v10 != Address0x0 and met_buy[x, y, v10, v20])
}

run transition__S23__a__S23__mediante_met_buy for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S25__mediante_met_buy for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S44__mediante_met_buy for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S49__mediante_met_buy for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S58__mediante_met_buy for 10 EstadoConcreto, 3 Deposit
pred transition__S23__a__S23__mediante_met_checkGoalReached{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS23[y] and
		v10 != Address0x0 and met_checkGoalReached[x, y, v10])
}

pred transition__S23__a__S25__mediante_met_checkGoalReached{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS25[y] and
		v10 != Address0x0 and met_checkGoalReached[x, y, v10])
}

pred transition__S23__a__S44__mediante_met_checkGoalReached{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS44[y] and
		v10 != Address0x0 and met_checkGoalReached[x, y, v10])
}

pred transition__S23__a__S49__mediante_met_checkGoalReached{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS49[y] and
		v10 != Address0x0 and met_checkGoalReached[x, y, v10])
}

pred transition__S23__a__S58__mediante_met_checkGoalReached{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS58[y] and
		v10 != Address0x0 and met_checkGoalReached[x, y, v10])
}

run transition__S23__a__S23__mediante_met_checkGoalReached for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S25__mediante_met_checkGoalReached for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S44__mediante_met_checkGoalReached for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S49__mediante_met_checkGoalReached for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S58__mediante_met_checkGoalReached for 10 EstadoConcreto, 3 Deposit
pred transition__S23__a__S23__mediante_met_refund{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS23[y] and
		v10 != Address0x0 and met_refund[x, y, v10])
}

pred transition__S23__a__S25__mediante_met_refund{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS25[y] and
		v10 != Address0x0 and met_refund[x, y, v10])
}

pred transition__S23__a__S44__mediante_met_refund{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS44[y] and
		v10 != Address0x0 and met_refund[x, y, v10])
}

pred transition__S23__a__S49__mediante_met_refund{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS49[y] and
		v10 != Address0x0 and met_refund[x, y, v10])
}

pred transition__S23__a__S58__mediante_met_refund{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS58[y] and
		v10 != Address0x0 and met_refund[x, y, v10])
}

run transition__S23__a__S23__mediante_met_refund for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S25__mediante_met_refund for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S44__mediante_met_refund for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S49__mediante_met_refund for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S58__mediante_met_refund for 10 EstadoConcreto, 3 Deposit
pred transition__S23__a__S23__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS23[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S23__a__S25__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS25[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S23__a__S44__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS44[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S23__a__S49__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS49[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S23__a__S58__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS23[x] and partitionS58[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

run transition__S23__a__S23__mediante_met_t for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S25__mediante_met_t for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S44__mediante_met_t for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S49__mediante_met_t for 10 EstadoConcreto, 3 Deposit
run transition__S23__a__S58__mediante_met_t for 10 EstadoConcreto, 3 Deposit

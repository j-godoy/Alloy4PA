abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Address{balance: Int}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressBeneficiary extends Address{}// concrete states
abstract sig EstadoConcreto {
	_deposited: Deposit,
	_beneficiary: Address,
	_superOwner: Address,
	_owner: Address,
	_balance: Int,
	_blockNumber: Int, //lo agrego para simular el paso del tiempo
	_state: lone State,
	_init: Bool
}

abstract sig State{}
one sig Active extends State {}
one sig Refunding extends State{}
one sig GoalReached extends State{}
one sig Closed extends State{}

fun LIMIT[]: Int {2}

sig Deposit{d: Address->lone Int}


pred invariante [e:EstadoConcreto] {
	e._init = True
	//En estado Active, la suma de depósitos debe ser igual al balance
	(e._state = Active or e._state = Refunding) implies sumatoria[e._deposited, e._balance]

	//Si se terminó el tiempo, debe suceder que balance < sumaDepósitos
	//Más especificamente, balance debe ser igual sumatoria de sumaDepósitos para k elementos (0<=k<#deposits)
	// e._state = Refunding implies sumatoriaSubSeq[e._deposited, e._balance]

	//Si state=Closed, entonces balance = 0
	e._state = Closed implies e._balance = 0

	e._beneficiary = Address0x0 implies no e._state

	all s:SumatoriaSeq, i:Int | some s.sec[i] implies s.sec[i] >= 0
	some s:SumatoriaSeq | s.sec = 0->0
	some s:SumatoriaSeq | s.sec = 0->0+1->0
	some s:SumatoriaSeq | s.sec = 0->1
	some s:SumatoriaSeq | s.sec = 0->1+1->0
	some s:SumatoriaSeq | s.sec = 0->2
	some s:SumatoriaSeq | s.sec = 0->2+1->0

	//No Negativos
	e._balance >= 0 and e._blockNumber >= 0
	all d0:Address | e._deposited.d[d0] >= 0

	//fixed size: Int= 0,1,2,3; max length=4
	all d0:Address | e._deposited.d[d0] >= 0 and e._deposited.d[d0] <= LIMIT[]
	#(e._deposited.d.Int) <= LIMIT[]
	e._owner != Address0x0
	e._superOwner != Address0x0
}

pred notInvariante[e: EstadoConcreto]{
	(not invariante[e])
	some sumaSeq: SumatoriaSeq, suma: Int | toSeq[e._deposited, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
}


fun sumof[s:seq Int]: Int {
	s=none->none implies 0
	else #s=0 implies 0
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
	// else s=0->0+1->0+2->0+3->0 implies 0
	// else s=0->0+1->0+2->0+3->1 implies 1
	// else s=0->0+1->0+2->0+3->2 implies 2
	// else s=0->0+1->0+2->0+3->3 implies 3
	// else s=0->0+1->0+2->1+3->0 implies 1
	// else s=0->0+1->0+2->1+3->1 implies 2
	// else s=0->0+1->0+2->1+3->2 implies 3
	// else s=0->0+1->0+2->1+3->3 implies 4
	// else s=0->0+1->0+2->2+3->0 implies 2
	// else s=0->0+1->0+2->2+3->1 implies 3
	// else s=0->0+1->0+2->2+3->2 implies 4
	// else s=0->0+1->0+2->2+3->3 implies 5
	// else s=0->0+1->0+2->3+3->0 implies 3
	// else s=0->0+1->0+2->3+3->1 implies 4
	// else s=0->0+1->0+2->3+3->2 implies 5
	// else s=0->0+1->0+2->3+3->3 implies 6
	// else s=0->0+1->1+2->0+3->0 implies 1
	// else s=0->0+1->1+2->0+3->1 implies 2
	// else s=0->0+1->1+2->0+3->2 implies 3
	// else s=0->0+1->1+2->0+3->3 implies 4
	// else s=0->0+1->1+2->1+3->0 implies 2
	// else s=0->0+1->1+2->1+3->1 implies 3
	// else s=0->0+1->1+2->1+3->2 implies 4
	// else s=0->0+1->1+2->1+3->3 implies 5
	// else s=0->0+1->1+2->2+3->0 implies 3
	// else s=0->0+1->1+2->2+3->1 implies 4
	// else s=0->0+1->1+2->2+3->2 implies 5
	// else s=0->0+1->1+2->2+3->3 implies 6
	// else s=0->0+1->1+2->3+3->0 implies 4
	// else s=0->0+1->1+2->3+3->1 implies 5
	// else s=0->0+1->1+2->3+3->2 implies 6
	// else s=0->0+1->1+2->3+3->3 implies 7
	// else s=0->0+1->2+2->0+3->0 implies 2
	// else s=0->0+1->2+2->0+3->1 implies 3
	// else s=0->0+1->2+2->0+3->2 implies 4
	// else s=0->0+1->2+2->0+3->3 implies 5
	// else s=0->0+1->2+2->1+3->0 implies 3
	// else s=0->0+1->2+2->1+3->1 implies 4
	// else s=0->0+1->2+2->1+3->2 implies 5
	// else s=0->0+1->2+2->1+3->3 implies 6
	// else s=0->0+1->2+2->2+3->0 implies 4
	// else s=0->0+1->2+2->2+3->1 implies 5
	// else s=0->0+1->2+2->2+3->2 implies 6
	// else s=0->0+1->2+2->2+3->3 implies 7
	// else s=0->0+1->2+2->3+3->0 implies 5
	// else s=0->0+1->2+2->3+3->1 implies 6
	// else s=0->0+1->2+2->3+3->2 implies 7
	// else s=0->0+1->2+2->3+3->3 implies 8
	// else s=0->0+1->3+2->0+3->0 implies 3
	// else s=0->0+1->3+2->0+3->1 implies 4
	// else s=0->0+1->3+2->0+3->2 implies 5
	// else s=0->0+1->3+2->0+3->3 implies 6
	// else s=0->0+1->3+2->1+3->0 implies 4
	// else s=0->0+1->3+2->1+3->1 implies 5
	// else s=0->0+1->3+2->1+3->2 implies 6
	// else s=0->0+1->3+2->1+3->3 implies 7
	// else s=0->0+1->3+2->2+3->0 implies 5
	// else s=0->0+1->3+2->2+3->1 implies 6
	// else s=0->0+1->3+2->2+3->2 implies 7
	// else s=0->0+1->3+2->2+3->3 implies 8
	// else s=0->0+1->3+2->3+3->0 implies 6
	// else s=0->0+1->3+2->3+3->1 implies 7
	// else s=0->0+1->3+2->3+3->2 implies 8
	// else s=0->0+1->3+2->3+3->3 implies 9
	// else s=0->1+1->0+2->0+3->0 implies 1
	// else s=0->1+1->0+2->0+3->1 implies 2
	// else s=0->1+1->0+2->0+3->2 implies 3
	// else s=0->1+1->0+2->0+3->3 implies 4
	// else s=0->1+1->0+2->1+3->0 implies 2
	// else s=0->1+1->0+2->1+3->1 implies 3
	// else s=0->1+1->0+2->1+3->2 implies 4
	// else s=0->1+1->0+2->1+3->3 implies 5
	// else s=0->1+1->0+2->2+3->0 implies 3
	// else s=0->1+1->0+2->2+3->1 implies 4
	// else s=0->1+1->0+2->2+3->2 implies 5
	// else s=0->1+1->0+2->2+3->3 implies 6
	// else s=0->1+1->0+2->3+3->0 implies 4
	// else s=0->1+1->0+2->3+3->1 implies 5
	// else s=0->1+1->0+2->3+3->2 implies 6
	// else s=0->1+1->0+2->3+3->3 implies 7
	// else s=0->1+1->1+2->0+3->0 implies 2
	// else s=0->1+1->1+2->0+3->1 implies 3
	// else s=0->1+1->1+2->0+3->2 implies 4
	// else s=0->1+1->1+2->0+3->3 implies 5
	// else s=0->1+1->1+2->1+3->0 implies 3
	// else s=0->1+1->1+2->1+3->1 implies 4
	// else s=0->1+1->1+2->1+3->2 implies 5
	// else s=0->1+1->1+2->1+3->3 implies 6
	// else s=0->1+1->1+2->2+3->0 implies 4
	// else s=0->1+1->1+2->2+3->1 implies 5
	// else s=0->1+1->1+2->2+3->2 implies 6
	// else s=0->1+1->1+2->2+3->3 implies 7
	// else s=0->1+1->1+2->3+3->0 implies 5
	// else s=0->1+1->1+2->3+3->1 implies 6
	// else s=0->1+1->1+2->3+3->2 implies 7
	// else s=0->1+1->1+2->3+3->3 implies 8
	// else s=0->1+1->2+2->0+3->0 implies 3
	// else s=0->1+1->2+2->0+3->1 implies 4
	// else s=0->1+1->2+2->0+3->2 implies 5
	// else s=0->1+1->2+2->0+3->3 implies 6
	// else s=0->1+1->2+2->1+3->0 implies 4
	// else s=0->1+1->2+2->1+3->1 implies 5
	// else s=0->1+1->2+2->1+3->2 implies 6
	// else s=0->1+1->2+2->1+3->3 implies 7
	// else s=0->1+1->2+2->2+3->0 implies 5
	// else s=0->1+1->2+2->2+3->1 implies 6
	// else s=0->1+1->2+2->2+3->2 implies 7
	// else s=0->1+1->2+2->2+3->3 implies 8
	// else s=0->1+1->2+2->3+3->0 implies 6
	// else s=0->1+1->2+2->3+3->1 implies 7
	// else s=0->1+1->2+2->3+3->2 implies 8
	// else s=0->1+1->2+2->3+3->3 implies 9
	// else s=0->1+1->3+2->0+3->0 implies 4
	// else s=0->1+1->3+2->0+3->1 implies 5
	// else s=0->1+1->3+2->0+3->2 implies 6
	// else s=0->1+1->3+2->0+3->3 implies 7
	// else s=0->1+1->3+2->1+3->0 implies 5
	// else s=0->1+1->3+2->1+3->1 implies 6
	// else s=0->1+1->3+2->1+3->2 implies 7
	// else s=0->1+1->3+2->1+3->3 implies 8
	// else s=0->1+1->3+2->2+3->0 implies 6
	// else s=0->1+1->3+2->2+3->1 implies 7
	// else s=0->1+1->3+2->2+3->2 implies 8
	// else s=0->1+1->3+2->2+3->3 implies 9
	// else s=0->1+1->3+2->3+3->0 implies 7
	// else s=0->1+1->3+2->3+3->1 implies 8
	// else s=0->1+1->3+2->3+3->2 implies 9
	// else s=0->1+1->3+2->3+3->3 implies 10
	// else s=0->2+1->0+2->0+3->0 implies 2
	// else s=0->2+1->0+2->0+3->1 implies 3
	// else s=0->2+1->0+2->0+3->2 implies 4
	// else s=0->2+1->0+2->0+3->3 implies 5
	// else s=0->2+1->0+2->1+3->0 implies 3
	// else s=0->2+1->0+2->1+3->1 implies 4
	// else s=0->2+1->0+2->1+3->2 implies 5
	// else s=0->2+1->0+2->1+3->3 implies 6
	// else s=0->2+1->0+2->2+3->0 implies 4
	// else s=0->2+1->0+2->2+3->1 implies 5
	// else s=0->2+1->0+2->2+3->2 implies 6
	// else s=0->2+1->0+2->2+3->3 implies 7
	// else s=0->2+1->0+2->3+3->0 implies 5
	// else s=0->2+1->0+2->3+3->1 implies 6
	// else s=0->2+1->0+2->3+3->2 implies 7
	// else s=0->2+1->0+2->3+3->3 implies 8
	// else s=0->2+1->1+2->0+3->0 implies 3
	// else s=0->2+1->1+2->0+3->1 implies 4
	// else s=0->2+1->1+2->0+3->2 implies 5
	// else s=0->2+1->1+2->0+3->3 implies 6
	// else s=0->2+1->1+2->1+3->0 implies 4
	// else s=0->2+1->1+2->1+3->1 implies 5
	// else s=0->2+1->1+2->1+3->2 implies 6
	// else s=0->2+1->1+2->1+3->3 implies 7
	// else s=0->2+1->1+2->2+3->0 implies 5
	// else s=0->2+1->1+2->2+3->1 implies 6
	// else s=0->2+1->1+2->2+3->2 implies 7
	// else s=0->2+1->1+2->2+3->3 implies 8
	// else s=0->2+1->1+2->3+3->0 implies 6
	// else s=0->2+1->1+2->3+3->1 implies 7
	// else s=0->2+1->1+2->3+3->2 implies 8
	// else s=0->2+1->1+2->3+3->3 implies 9
	// else s=0->2+1->2+2->0+3->0 implies 4
	// else s=0->2+1->2+2->0+3->1 implies 5
	// else s=0->2+1->2+2->0+3->2 implies 6
	// else s=0->2+1->2+2->0+3->3 implies 7
	// else s=0->2+1->2+2->1+3->0 implies 5
	// else s=0->2+1->2+2->1+3->1 implies 6
	// else s=0->2+1->2+2->1+3->2 implies 7
	// else s=0->2+1->2+2->1+3->3 implies 8
	// else s=0->2+1->2+2->2+3->0 implies 6
	// else s=0->2+1->2+2->2+3->1 implies 7
	// else s=0->2+1->2+2->2+3->2 implies 8
	// else s=0->2+1->2+2->2+3->3 implies 9
	// else s=0->2+1->2+2->3+3->0 implies 7
	// else s=0->2+1->2+2->3+3->1 implies 8
	// else s=0->2+1->2+2->3+3->2 implies 9
	// else s=0->2+1->2+2->3+3->3 implies 10
	// else s=0->2+1->3+2->0+3->0 implies 5
	// else s=0->2+1->3+2->0+3->1 implies 6
	// else s=0->2+1->3+2->0+3->2 implies 7
	// else s=0->2+1->3+2->0+3->3 implies 8
	// else s=0->2+1->3+2->1+3->0 implies 6
	// else s=0->2+1->3+2->1+3->1 implies 7
	// else s=0->2+1->3+2->1+3->2 implies 8
	// else s=0->2+1->3+2->1+3->3 implies 9
	// else s=0->2+1->3+2->2+3->0 implies 7
	// else s=0->2+1->3+2->2+3->1 implies 8
	// else s=0->2+1->3+2->2+3->2 implies 9
	// else s=0->2+1->3+2->2+3->3 implies 10
	// else s=0->2+1->3+2->3+3->0 implies 8
	// else s=0->2+1->3+2->3+3->1 implies 9
	// else s=0->2+1->3+2->3+3->2 implies 10
	// else s=0->2+1->3+2->3+3->3 implies 11
	// else s=0->3+1->0+2->0+3->0 implies 3
	// else s=0->3+1->0+2->0+3->1 implies 4
	// else s=0->3+1->0+2->0+3->2 implies 5
	// else s=0->3+1->0+2->0+3->3 implies 6
	// else s=0->3+1->0+2->1+3->0 implies 4
	// else s=0->3+1->0+2->1+3->1 implies 5
	// else s=0->3+1->0+2->1+3->2 implies 6
	// else s=0->3+1->0+2->1+3->3 implies 7
	// else s=0->3+1->0+2->2+3->0 implies 5
	// else s=0->3+1->0+2->2+3->1 implies 6
	// else s=0->3+1->0+2->2+3->2 implies 7
	// else s=0->3+1->0+2->2+3->3 implies 8
	// else s=0->3+1->0+2->3+3->0 implies 6
	// else s=0->3+1->0+2->3+3->1 implies 7
	// else s=0->3+1->0+2->3+3->2 implies 8
	// else s=0->3+1->0+2->3+3->3 implies 9
	// else s=0->3+1->1+2->0+3->0 implies 4
	// else s=0->3+1->1+2->0+3->1 implies 5
	// else s=0->3+1->1+2->0+3->2 implies 6
	// else s=0->3+1->1+2->0+3->3 implies 7
	// else s=0->3+1->1+2->1+3->0 implies 5
	// else s=0->3+1->1+2->1+3->1 implies 6
	// else s=0->3+1->1+2->1+3->2 implies 7
	// else s=0->3+1->1+2->1+3->3 implies 8
	// else s=0->3+1->1+2->2+3->0 implies 6
	// else s=0->3+1->1+2->2+3->1 implies 7
	// else s=0->3+1->1+2->2+3->2 implies 8
	// else s=0->3+1->1+2->2+3->3 implies 9
	// else s=0->3+1->1+2->3+3->0 implies 7
	// else s=0->3+1->1+2->3+3->1 implies 8
	// else s=0->3+1->1+2->3+3->2 implies 9
	// else s=0->3+1->1+2->3+3->3 implies 10
	// else s=0->3+1->2+2->0+3->0 implies 5
	// else s=0->3+1->2+2->0+3->1 implies 6
	// else s=0->3+1->2+2->0+3->2 implies 7
	// else s=0->3+1->2+2->0+3->3 implies 8
	// else s=0->3+1->2+2->1+3->0 implies 6
	// else s=0->3+1->2+2->1+3->1 implies 7
	// else s=0->3+1->2+2->1+3->2 implies 8
	// else s=0->3+1->2+2->1+3->3 implies 9
	// else s=0->3+1->2+2->2+3->0 implies 7
	// else s=0->3+1->2+2->2+3->1 implies 8
	// else s=0->3+1->2+2->2+3->2 implies 9
	// else s=0->3+1->2+2->2+3->3 implies 10
	// else s=0->3+1->2+2->3+3->0 implies 8
	// else s=0->3+1->2+2->3+3->1 implies 9
	// else s=0->3+1->2+2->3+3->2 implies 10
	// else s=0->3+1->2+2->3+3->3 implies 11
	// else s=0->3+1->3+2->0+3->0 implies 6
	// else s=0->3+1->3+2->0+3->1 implies 7
	// else s=0->3+1->3+2->0+3->2 implies 8
	// else s=0->3+1->3+2->0+3->3 implies 9
	// else s=0->3+1->3+2->1+3->0 implies 7
	// else s=0->3+1->3+2->1+3->1 implies 8
	// else s=0->3+1->3+2->1+3->2 implies 9
	// else s=0->3+1->3+2->1+3->3 implies 10
	// else s=0->3+1->3+2->2+3->0 implies 8
	// else s=0->3+1->3+2->2+3->1 implies 9
	// else s=0->3+1->3+2->2+3->2 implies 10
	// else s=0->3+1->3+2->2+3->3 implies 11
	// else s=0->3+1->3+2->3+3->0 implies 9
	// else s=0->3+1->3+2->3+3->1 implies 10
	// else s=0->3+1->3+2->3+3->2 implies 11
	// else s=0->3+1->3+2->3+3->3 implies 12
	else 0
}

pred sumatoria [s: set Deposit, suma: Int] {
	some sumaSeq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
}

pred sumatoriaSubSeq [s: set Deposit, suma: Int] {
	some sumaSeq: SumatoriaSeq, subseq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and
			subSeq[sumaSeq.sec, subseq.sec] and sumof[subseq.sec] = suma
}

pred subSeq [original: seq Int, subseq: seq Int] {
	#subseq <= #original
	all i: Int | some subseq[i] implies subseq[i] in original.elems
	all i: Int | some subseq[i] implies #subseq.i <= #original.i
}

pred toSeq [s: set Deposit, ret: seq Int] {
	all d0: s.d.Int | some i: Int | ret[i]=s.d[d0] //Todo elemento del set está en la seq
	all i: Int | some ret[i] implies some d0: s.d.Int | s.d[d0]=ret[i]//Todo elemento de la seq está en el set
	all i: Int | #(s.d.i) = #(ret.i) //#elem(set,e) = #elem(seq,e)
	#(s.d.Int)=#(ret)
}

sig SumatoriaSeq {sec: seq Int}

pred pre_constructor[ein: EstadoConcreto] {
	ein._init = False
	//ein._deposited.d = Address0x0->0
	ein._beneficiary = Address0x0
	ein._superOwner = Address0x0
	ein._owner = Address0x0
	ein._balance = 0
	no ein._state
	#ein._deposited.d = 0
	ein._balance = 0
}

pred pre_params_constructor [ein: EstadoConcreto, sender:Address, superOwner: Address, beneficiary: Address] {
	sender != Address0x0
	beneficiary != Address0x0
	superOwner != Address0x0
}

pred met_constructor [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, superOwner: Address, beneficiary: Address] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, superOwner, beneficiary]

	//Post
	eout._beneficiary = beneficiary
	eout._superOwner = superOwner
	eout._state = Active
	eout._owner = sender
	eout._init = True

	eout._deposited = ein._deposited
	//eout._beneficiary = ein._beneficiary
	//eout._superOwner = ein._superOWner
	//eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}


pred pre_transferOwnership [ein: EstadoConcreto] {
	some ein._state
	ein._init = True
}

pred pre_params_transferOwnership [ein: EstadoConcreto, sender:Address, recipient: Address] {
	ein._owner = sender
}

pred met_transferOwnership [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, recipient: Address] {
	///PRE
	pre_transferOwnership[ein]
	pre_params_transferOwnership[ein, sender, recipient]
	
	//POST
	eout._owner = recipient

	eout._deposited = ein._deposited
	eout._beneficiary = ein._beneficiary
	eout._superOwner = ein._superOwner
	//eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
}


pred pre_deposit [ein: EstadoConcreto] {
	ein._state = Active or ein._state = GoalReached
	ein._init = True
}

pred pre_params_deposit [ein: EstadoConcreto, sender:Address, investor: Address, value: Int] {
	sender = ein._owner
	value <= LIMIT[] //por la limitación de la sumatoria
	ein._deposited.d[investor].add[value] <= LIMIT[]
}

pred met_deposit [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, investor: Address, value: Int] {
	//PRE
	pre_deposit [ein]
	pre_params_deposit[ein, sender, investor, value]

	//POST
	eout._deposited.d= ein._deposited.d++investor->ein._deposited.d[investor].add[value]
	eout._balance = ein._balance.add[value]

	//eout._deposited = ein._deposited
	eout._beneficiary = ein._beneficiary
	eout._superOwner = ein._superOwner
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	//eout._balance = ein._balance
	eout._init = ein._init
}


pred pre_setGoalReached [ein: EstadoConcreto] {
	ein._state = Active
	ein._init = True
}

pred pre_params_setGoalReached [ein: EstadoConcreto, sender:Address, value: Int] {
	sender = ein._owner
}

pred met_setGoalReached [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int] {
	//PRE
	pre_setGoalReached[ein]
	pre_params_setGoalReached[ein, sender, value]
	
	//POST
	eout._state = GoalReached

	eout._deposited = ein._deposited
	eout._beneficiary = ein._beneficiary
	eout._superOwner = ein._superOwner
	eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
}

pred pre_withdraw [ein: EstadoConcreto] {
	ein._state = GoalReached
	ein._init = True
}

pred pre_params_withdraw [ein: EstadoConcreto, sender:Address, amount: Int] {
	ein._superOwner = sender
	amount > 0
	amount <= ein._balance
}

pred met_withdraw [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, amount: Int] {
	//PRE
	pre_withdraw[ein]
	pre_params_withdraw[ein, sender, amount]

	//POST
	eout._balance = ein._balance.sub[amount]
	//beneficiary.transfer(_amount);

	eout._deposited = ein._deposited
	eout._beneficiary = ein._beneficiary
	eout._superOwner = ein._superOwner
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	//eout._balance = ein._balance
	eout._init = ein._init
}


pred pre_withdrawAll [ein: EstadoConcreto] {
	ein._state = GoalReached
	ein._init = True
}

pred pre_params_withdrawAll [ein: EstadoConcreto, sender:Address] {
	ein._owner = sender
}

pred met_withdrawAll [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_withdrawAll[ein]
	pre_params_withdrawAll[ein, sender]
	
	//POST
	eout._balance = 0
	//beneficiary.transfer(balance);

	eout._deposited = ein._deposited
	eout._beneficiary = ein._beneficiary
	eout._superOwner = ein._superOwner
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	//eout._balance = ein._balance
	eout._init = ein._init
}


pred pre_close [ein: EstadoConcreto] {
	ein._state = GoalReached
	ein._init = True
}

pred pre_params_close [ein: EstadoConcreto, sender:Address] {
	ein._owner = sender
}


pred met_close [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_close[ein]
	pre_params_close[ein, sender]

	//POST
	eout._balance = 0 // withdrawAll()
	eout._state = Closed

	eout._deposited = ein._deposited
	eout._beneficiary = ein._beneficiary
	eout._superOwner = ein._superOwner
	eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	//eout._balance = ein._balance
	eout._init = ein._init
}


pred pre_enableRefunds [ein: EstadoConcreto] {
	ein._state = Active
	ein._init = True
}

pred pre_params_enableRefunds [ein: EstadoConcreto, sender:Address] {
	ein._owner = sender
}

pred met_enableRefunds [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_enableRefunds[ein]
	pre_params_enableRefunds[ein, sender]

	//POST
	eout._state = Refunding

	eout._deposited = ein._deposited
	eout._beneficiary = ein._beneficiary
	eout._superOwner = ein._superOwner
	eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
}


pred pre_refund [ein: EstadoConcreto] {
	ein._state = Refunding
	ein._init = True
}

pred pre_params_refund [ein: EstadoConcreto, sender:Address, investor: Address] {
}

pred met_refund [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, investor: Address] {
	//PRE
	pre_refund[ein]
	pre_params_refund[ein, sender, investor]

	eout._deposited.d = ein._deposited.d++investor->0
	eout._balance = ein._balance.sub[ein._deposited.d[investor]]

	//eout._deposited = ein._deposited
	eout._beneficiary = ein._beneficiary
	eout._superOwner = ein._superOwner
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	//eout._balance = ein._balance
	eout._init = ein._init
}

pred pre_t[ein: EstadoConcreto] {
	ein._init = True
}

pred pre_params_t[ein: EstadoConcreto, sender: Address] {
	// timeElapsed >= 0
}

pred met_t[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_t[ein]
	pre_params_t[ein, sender]

	eout._deposited = ein._deposited
	eout._beneficiary = ein._beneficiary
	eout._superOwner = ein._superOwner
	eout._owner = ein._owner
	eout._state = ein._state
	eout._balance = ein._balance
	ein._blockNumber < max => eout._blockNumber = ein._blockNumber.add[1] else eout._blockNumber = ein._blockNumber
	eout._init = ein._init
}



//////////////////////////////////////////////////////////////////////////////////////
// I add a predicate for each possible theoretical partition //
//////////////////////////////////////////////////////////////////////////////////////

pred partitionS00[e: EstadoConcreto]{
	pre_constructor[e]
}


pred partitionINV[e: EstadoConcreto]{
	notInvariante[e]
}






pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS09[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS10[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS11[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS12[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS13[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS14[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS15[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS16[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS17[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS18[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS19[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS20[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS21[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS22[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS23[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS24[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS25[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS26[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS27[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS28[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS29[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS30[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS31[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS32[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS33[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS34[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS35[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS36[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS37[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS38[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS39[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS40[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS41[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS42[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS43[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS44[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS45[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS46[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS47[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS48[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS49[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS50[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS51[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS52[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS53[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS54[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS55[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS56[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS57[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS58[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS59[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS60[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS61[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS62[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS63[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS64[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS65[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS66[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS67[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS68[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS69[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS70[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS71[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS72[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS73[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS74[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS75[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS76[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS77[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS78[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS79[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS80[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS81[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS82[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS83[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS84[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS85[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS86[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS87[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS88[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS89[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS90[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS91[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS92[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS93[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS94[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS95[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS96[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS97[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS98[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS99[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS100[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS101[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS102[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS103[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS104[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS105[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS106[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS107[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS108[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS109[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS110[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS111[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS112[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS113[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS114[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS115[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS116[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS117[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS118[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS119[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS120[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS121[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS122[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS123[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS124[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS125[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS126[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS127[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS128[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS129[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS130[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS131[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS132[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS133[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS134[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS135[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS136[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS137[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS138[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS139[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS140[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS141[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS142[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS143[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS144[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS145[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS146[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS147[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS148[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS149[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS150[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS151[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS152[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS153[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS154[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS155[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS156[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS157[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS158[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS159[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS160[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS161[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS162[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS163[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS164[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS165[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS166[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS167[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS168[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS169[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS170[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS171[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS172[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS173[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS174[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS175[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS176[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS177[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS178[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS179[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS180[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS181[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS182[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS183[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS184[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS185[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS186[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS187[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS188[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS189[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS190[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS191[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS192[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS193[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS194[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS195[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS196[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS197[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS198[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS199[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS200[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS201[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS202[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS203[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS204[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS205[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS206[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS207[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS208[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS209[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS210[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS211[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS212[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS213[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS214[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS215[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS216[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS217[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS218[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS219[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS220[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS221[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS222[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS223[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS224[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS225[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS226[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS227[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS228[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS229[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS230[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS231[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS232[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS233[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS234[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS235[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS236[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS237[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS238[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS239[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS240[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS241[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS242[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS243[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS244[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS245[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS246[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS247[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS248[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS249[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS250[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS251[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS252[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS253[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS254[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS255[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS256[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS257[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS258[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS259[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS260[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS261[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS262[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS263[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS264[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS265[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS266[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS267[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS268[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS269[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS270[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS271[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS272[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS273[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS274[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS275[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS276[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS277[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS278[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS279[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS280[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS281[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS282[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS283[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS284[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS285[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS286[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS287[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS288[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS289[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS290[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS291[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS292[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS293[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS294[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS295[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS296[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS297[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS298[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS299[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS300[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS301[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS302[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS303[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS304[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS305[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS306[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS307[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS308[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS309[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS310[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS311[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS312[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS313[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS314[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS315[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS316[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS317[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS318[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS319[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS320[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS321[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS322[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS323[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS324[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS325[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS326[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS327[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS328[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS329[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS330[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS331[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS332[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS333[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS334[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS335[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS336[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS337[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS338[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS339[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS340[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS341[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS342[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS343[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS344[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS345[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS346[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS347[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS348[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS349[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS350[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS351[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS352[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS353[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS354[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS355[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS356[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS357[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS358[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS359[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS360[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS361[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS362[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS363[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS364[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS365[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS366[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS367[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS368[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS369[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS370[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS371[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS372[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS373[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS374[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS375[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS376[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS377[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS378[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS379[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS380[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS381[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS382[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS383[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS384[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS385[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS386[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS387[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS388[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS389[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS390[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS391[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS392[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS393[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS394[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS395[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS396[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS397[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS398[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS399[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS400[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS401[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS402[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS403[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS404[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS405[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS406[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS407[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS408[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS409[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS410[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS411[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS412[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS413[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS414[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS415[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS416[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS417[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS418[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS419[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS420[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS421[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS422[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS423[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS424[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS425[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS426[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS427[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS428[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS429[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS430[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS431[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS432[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS433[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS434[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS435[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS436[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS437[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS438[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS439[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS440[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS441[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS442[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS443[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS444[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS445[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS446[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS447[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS448[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS449[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS450[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS451[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS452[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS453[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS454[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS455[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS456[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS457[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS458[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS459[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS460[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS461[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS462[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS463[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS464[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS465[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS466[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS467[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS468[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS469[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS470[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS471[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS472[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS473[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS474[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS475[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS476[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS477[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS478[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS479[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS480[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS481[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS482[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS483[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS484[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS485[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS486[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS487[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS488[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS489[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS490[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS491[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS492[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS493[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS494[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS495[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS496[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS497[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS498[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS499[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS500[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS501[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS502[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS503[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS504[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS505[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS506[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS507[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS508[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS509[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS510[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS511[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS512[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS513[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS514[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS515[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS516[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS517[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS518[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS519[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS520[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS521[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS522[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS523[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS524[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS525[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS526[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS527[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS528[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS529[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS530[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS531[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS532[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS533[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS534[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS535[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS536[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS537[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS538[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS539[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS540[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS541[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS542[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS543[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS544[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS545[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS546[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS547[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS548[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS549[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS550[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS551[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS552[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS553[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS554[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS555[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS556[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS557[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS558[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS559[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS560[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS561[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS562[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS563[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS564[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS565[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS566[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS567[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS568[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS569[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS570[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS571[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS572[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS573[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS574[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS575[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS576[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS577[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS578[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS579[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS580[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS581[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS582[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS583[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS584[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS585[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS586[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS587[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS588[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS589[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS590[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS591[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS592[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS593[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS594[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS595[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS596[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS597[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS598[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS599[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS600[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS601[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS602[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS603[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS604[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS605[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS606[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS607[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS608[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS609[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS610[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS611[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS612[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS613[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS614[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS615[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS616[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS617[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS618[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS619[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS620[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS621[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS622[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS623[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS624[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS625[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS626[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS627[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS628[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS629[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS630[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS631[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS632[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS633[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS634[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS635[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS636[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS637[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS638[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS639[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS640[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS641[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS642[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS643[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS644[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS645[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS646[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS647[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS648[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS649[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS650[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS651[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS652[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS653[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS654[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS655[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS656[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS657[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS658[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS659[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS660[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS661[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS662[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS663[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS664[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS665[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS666[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS667[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS668[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS669[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS670[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS671[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS672[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS673[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS674[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS675[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS676[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS677[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS678[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS679[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS680[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS681[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS682[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS683[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS684[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS685[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS686[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS687[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS688[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS689[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS690[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS691[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS692[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS693[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS694[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS695[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS696[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS697[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS698[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS699[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS700[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS701[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS702[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS703[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS704[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS705[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS706[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS707[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS708[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS709[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS710[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS711[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS712[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS713[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS714[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS715[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS716[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS717[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS718[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS719[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS720[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS721[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS722[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS723[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS724[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS725[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS726[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS727[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS728[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS729[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS730[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS731[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS732[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS733[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS734[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS735[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS736[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS737[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS738[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS739[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS740[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS741[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS742[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS743[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS744[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS745[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS746[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS747[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS748[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS749[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS750[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS751[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS752[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS753[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS754[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS755[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS756[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS757[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS758[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS759[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS760[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS761[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS762[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS763[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS764[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS765[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS766[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS767[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS768[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS769[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS770[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS771[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS772[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS773[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS774[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS775[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS776[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS777[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS778[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS779[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS780[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS781[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS782[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS783[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS784[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS785[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS786[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS787[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS788[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS789[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS790[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS791[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS792[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS793[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS794[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS795[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS796[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS797[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS798[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS799[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS800[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS801[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS802[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS803[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS804[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS805[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS806[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS807[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS808[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS809[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS810[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS811[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS812[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS813[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS814[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS815[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS816[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS817[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS818[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS819[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS820[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS821[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS822[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS823[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS824[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS825[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS826[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS827[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS828[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS829[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS830[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS831[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS832[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS833[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS834[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS835[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS836[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS837[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS838[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS839[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS840[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS841[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS842[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS843[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS844[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS845[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS846[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS847[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS848[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS849[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS850[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS851[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS852[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS853[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS854[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS855[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS856[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS857[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS858[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS859[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS860[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS861[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS862[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS863[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS864[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS865[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS866[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS867[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS868[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS869[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS870[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS871[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS872[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS873[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS874[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS875[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS876[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS877[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS878[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS879[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS880[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS881[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS882[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS883[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS884[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS885[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS886[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS887[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS888[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS889[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS890[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS891[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS892[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS893[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS894[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS895[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS896[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS897[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS898[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS899[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS900[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS901[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS902[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS903[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS904[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS905[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS906[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS907[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS908[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS909[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS910[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS911[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS912[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS913[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS914[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS915[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS916[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS917[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS918[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS919[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS920[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS921[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS922[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS923[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS924[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS925[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS926[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS927[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS928[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS929[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS930[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS931[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS932[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS933[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS934[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS935[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS936[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS937[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS938[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS939[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS940[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS941[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS942[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS943[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS944[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS945[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS946[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS947[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS948[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS949[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS950[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS951[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS952[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS953[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS954[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS955[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS956[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS957[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS958[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS959[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS960[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS961[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS962[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS963[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS964[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS965[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS966[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS967[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS968[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS969[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and pre_t[e]
}

pred partitionS970[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS971[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS972[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS973[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS974[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS975[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS976[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS977[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS978[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS979[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS980[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS981[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS982[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS983[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS984[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS985[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS986[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS987[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS988[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS989[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS990[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS991[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS992[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS993[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS994[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS995[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS996[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS997[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS998[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS999[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1000[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1001[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1002[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1003[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1004[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1005[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS1006[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS1007[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1008[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1009[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1010[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1011[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1012[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1013[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1014[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and pre_t[e]
}

pred partitionS1015[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and pre_refund [e] and not pre_t[e]
}

pred partitionS1016[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1017[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1018[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1019[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1020[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1021[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1022[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1023[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}

pred partitionS1024[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_transferOwnership [e] and not pre_deposit [e] and not pre_setGoalReached [e] and not pre_withdraw [e] and not pre_withdrawAll [e] and not pre_close [e] and not pre_enableRefunds [e] and not pre_refund [e] and not pre_t[e]
}




pred transition__S499__a__S238__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS238[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S499__a__S499__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS499[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S499__a__S905__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS905[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S499__a__S997__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS997[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S499__a__S1014__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS1014[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

run transition__S499__a__S238__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S499__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S905__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S997__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S1014__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S499__a__S238__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS499[x] and partitionS238[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S499__a__S499__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS499[x] and partitionS499[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S499__a__S905__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS499[x] and partitionS905[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S499__a__S997__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS499[x] and partitionS997[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S499__a__S1014__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS499[x] and partitionS1014[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

run transition__S499__a__S238__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S499__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S905__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S997__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S1014__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S499__a__S238__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS238[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S499__a__S499__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS499[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S499__a__S905__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS905[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S499__a__S997__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS997[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S499__a__S1014__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS1014[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

run transition__S499__a__S238__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S499__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S905__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S997__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S1014__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S499__a__S238__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS238[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S499__a__S499__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS499[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S499__a__S905__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS905[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S499__a__S997__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS997[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S499__a__S1014__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS499[x] and partitionS1014[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

run transition__S499__a__S238__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S499__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S905__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S997__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S1014__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S499__a__S238__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS238[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S499__a__S499__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS499[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S499__a__S905__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS905[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S499__a__S997__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS997[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S499__a__S1014__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS1014[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

run transition__S499__a__S238__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S499__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S905__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S997__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S1014__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S499__a__S238__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS238[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S499__a__S499__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS499[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S499__a__S905__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS905[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S499__a__S997__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS997[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S499__a__S1014__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS1014[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

run transition__S499__a__S238__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S499__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S905__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S997__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S1014__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S499__a__S238__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS238[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S499__a__S499__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS499[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S499__a__S905__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS905[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S499__a__S997__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS997[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S499__a__S1014__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS1014[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

run transition__S499__a__S238__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S499__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S905__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S997__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S1014__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S499__a__S238__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS238[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S499__a__S499__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS499[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S499__a__S905__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS905[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S499__a__S997__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS997[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S499__a__S1014__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS499[x] and partitionS1014[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

run transition__S499__a__S238__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S499__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S905__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S997__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S1014__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S499__a__S238__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS238[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S499__a__S499__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS499[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S499__a__S905__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS905[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S499__a__S997__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS997[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S499__a__S1014__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS499[x] and partitionS1014[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

run transition__S499__a__S238__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S499__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S905__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S997__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S499__a__S1014__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq

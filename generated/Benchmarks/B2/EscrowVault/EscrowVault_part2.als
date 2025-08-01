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


pred partitionS01[e:EstadoConcreto] {
	(invariante[e])
	e._state = Active
}

pred partitionS02[e:EstadoConcreto] {
	(invariante[e])
	e._state = Refunding
}

pred partitionS03[e:EstadoConcreto] {
	(invariante[e])
	e._state = GoalReached
}

pred partitionS04[e:EstadoConcreto] {
	(invariante[e])
	e._state = Closed
}







pred transition__S02__a__S01__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S02__a__S02__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S02__a__S03__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S02__a__S04__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S03__a__S01__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S03__a__S02__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S03__a__S03__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

pred transition__S03__a__S04__mediante_met_transferOwnership {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS04[y] and
		v10 != Address0x0 and met_transferOwnership [x, y, v10, v11])
}

run transition__S02__a__S01__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S04__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S01__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S02__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S03__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S04__mediante_met_transferOwnership  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S02__a__S02__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S02__a__S03__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S02__a__S04__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S03__a__S01__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S03__a__S02__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S03__a__S03__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

pred transition__S03__a__S04__mediante_met_deposit {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS03[x] and partitionS04[y] and
		v10 != Address0x0 and met_deposit [x, y, v10, v11, v20])
}

run transition__S02__a__S01__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S04__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S01__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S02__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S03__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S04__mediante_met_deposit  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S02__a__S02__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S02__a__S03__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S02__a__S04__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S03__a__S01__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S03__a__S02__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S03__a__S03__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

pred transition__S03__a__S04__mediante_met_setGoalReached {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS03[x] and partitionS04[y] and
		v10 != Address0x0 and met_setGoalReached [x, y, v10, v20])
}

run transition__S02__a__S01__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S04__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S01__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S02__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S03__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S04__mediante_met_setGoalReached  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S02__a__S02__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S02__a__S03__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S02__a__S04__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S03__a__S01__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S03__a__S02__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S03__a__S03__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

pred transition__S03__a__S04__mediante_met_withdraw {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS03[x] and partitionS04[y] and
		v10 != Address0x0 and met_withdraw [x, y, v10, v20])
}

run transition__S02__a__S01__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S04__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S01__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S02__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S03__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S04__mediante_met_withdraw  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S02__a__S02__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S02__a__S03__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S02__a__S04__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S03__a__S01__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S03__a__S02__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S03__a__S03__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

pred transition__S03__a__S04__mediante_met_withdrawAll {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS04[y] and
		v10 != Address0x0 and met_withdrawAll [x, y, v10])
}

run transition__S02__a__S01__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S04__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S01__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S02__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S03__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S04__mediante_met_withdrawAll  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S02__a__S02__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S02__a__S03__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S02__a__S04__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S03__a__S01__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S03__a__S02__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S03__a__S03__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

pred transition__S03__a__S04__mediante_met_close {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS04[y] and
		v10 != Address0x0 and met_close [x, y, v10])
}

run transition__S02__a__S01__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S04__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S01__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S02__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S03__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S04__mediante_met_close  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S02__a__S02__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S02__a__S03__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S02__a__S04__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S03__a__S01__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S03__a__S02__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S03__a__S03__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

pred transition__S03__a__S04__mediante_met_enableRefunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS04[y] and
		v10 != Address0x0 and met_enableRefunds [x, y, v10])
}

run transition__S02__a__S01__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S04__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S01__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S02__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S03__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S04__mediante_met_enableRefunds  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S02__a__S02__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S02__a__S03__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S02__a__S04__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S03__a__S01__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S03__a__S02__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S03__a__S03__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

pred transition__S03__a__S04__mediante_met_refund {
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS03[x] and partitionS04[y] and
		v10 != Address0x0 and met_refund [x, y, v10, v11])
}

run transition__S02__a__S01__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S04__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S01__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S02__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S03__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S04__mediante_met_refund  for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S02__a__S02__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S02__a__S03__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S02__a__S04__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS04[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S03__a__S01__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS01[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S03__a__S02__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS02[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S03__a__S03__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS03[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S03__a__S04__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS03[x] and partitionS04[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

run transition__S02__a__S01__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S04__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S01__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S02__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S03__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S03__a__S04__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq

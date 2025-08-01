abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressBeneficiary extends Address{}

sig Deposit{d: Address->lone Int}// concrete states
abstract sig EstadoConcreto {
	_beneficiary: Address,
	_deposits: lone Deposit,
	_owner: Address,
	_balance: Int,
	_blockNumber: Int, //lo agrego para simular el paso del tiempo
	_state: lone State,
	_beneficiaryWithdrawal: Bool,
	_init: Bool
}

abstract sig State{}
one sig Active extends State {}
one sig Refunding extends State{}
one sig Closed extends State{}

fun LIMIT[]: Int {2}

pred invariante[e:EstadoConcreto] {
	e._init = True
	e._owner != Address0x0
	//En estado Active, la suma de depósitos debe ser igual al balance
	// (e._state = Active or e._state = Refunding or e._state = Closed) implies sumatoria[e._deposits, e._balance]
	sumatoria[e._deposits, e._balance] or (e._beneficiaryWithdrawal = True and e._balance = 0)

	//Si se terminó el tiempo, debe suceder que balance < sumaDepósitos
	//Más especificamente, balance debe ser igual sumatoria de sumaDepósitos para k elementos (0<=k<#deposits)

	e._balance = 0 implies
			(
				(all a:Address | a in (e._deposits.d).Int implies e._deposits.d[a] = 0)
				or
				e._beneficiaryWithdrawal = True
			)

	// e._state = Refunding implies sumatoriaSubSeq[e._deposits, e._balance]
	all s:SumatoriaSeq, i:Int | some s.sec[i] implies s.sec[i] >= 0
	some s:SumatoriaSeq | s.sec = 0->0
	some s:SumatoriaSeq | s.sec = 0->0+1->0
	some s:SumatoriaSeq | s.sec = 0->1
	some s:SumatoriaSeq | s.sec = 0->1+1->0
	some s:SumatoriaSeq | s.sec = 0->2
	some s:SumatoriaSeq | s.sec = 0->2+1->0

	//No Negativos
	e._balance >= 0 and e._blockNumber >= 0
	all d0:Address | e._deposits.d[d0] >= 0

	//fixed size: Int= 0,1,2,3; max length=4
	all d0:Address | e._deposits.d[d0] >= 0 and e._deposits.d[d0] <= LIMIT[]
	#(e._deposits.d.Int) <= LIMIT[]
}

pred notInvariante[e: EstadoConcreto]{
	(not invariante[e])
	some sumaSeq: SumatoriaSeq, suma: Int | toSeq[e._deposits, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
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

pred sumatoria[s: set Deposit, suma: Int] {
	some sumaSeq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
}

pred sumatoriaSubSeq[s: set Deposit, suma: Int] {
	some sumaSeq: SumatoriaSeq, subseq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and
			subSeq[sumaSeq.sec, subseq.sec] and sumof[subseq.sec] = suma
}

pred subSeq[original: seq Int, subseq: seq Int] {
	#subseq <= #original
	all i: Int | some subseq[i] implies subseq[i] in original.elems
	all i: Int | some subseq[i] implies #subseq.i <= #original.i
}

pred toSeq[s: set Deposit, ret: seq Int] {
	all d0: s.d.Int | some i: Int | ret[i]=s.d[d0] //Todo elemento del set está en la seq
	all i: Int | some ret[i] implies some d0: s.d.Int | s.d[d0]=ret[i]//Todo elemento de la seq está en el set
	all i: Int | #(s.d.i) = #(ret.i) //#elem(set,e) = #elem(seq,e)
	#(s.d.Int)=#(ret)
}

sig SumatoriaSeq {sec: seq Int}

pred pre_constructor[ein: EstadoConcreto] {
	ein._init = False
	ein._beneficiaryWithdrawal = False
	ein._balance >= 0
	ein._blockNumber >= 0
	no ein._deposits
	no ein._state
	ein._beneficiary = Address0x0
	ein._owner = Address0x0
	ein._balance = 0
	// beneficiary != Address0x0
	// sender != Address0x0
	all s:SumatoriaSeq, i:Int | some s.sec[i] implies s.sec[i] >= 0
	some s:SumatoriaSeq | s.sec = 0->0
	some s:SumatoriaSeq | s.sec = 0->0+1->0
	some s:SumatoriaSeq | s.sec = 0->1
	some s:SumatoriaSeq | s.sec = 0->1+1->0
	some s:SumatoriaSeq | s.sec = 0->2
	some s:SumatoriaSeq | s.sec = 0->2+1->0
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address, beneficiary: Address] {
	ein._beneficiary = Address0x0
	ein._owner = Address0x0
	ein._balance = 0
	beneficiary != Address0x0
	sender != Address0x0
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, beneficiary: Address] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, beneficiary]


	//Post
	eout._beneficiary = beneficiary
	eout._owner = sender
	eout._state = Active
	eout._init = True

	eout._deposits = ein._deposits
	//eout._beneficiary = ein._beneficiary
	//eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	eout._beneficiaryWithdrawal = ein._beneficiaryWithdrawal
	eout._balance = ein._balance
}


pred pre_deposit[ein: EstadoConcreto] {
	ein._state = Active
	ein._init = True
}

pred pre_params_deposit[ein: EstadoConcreto, sender:Address, refundee: Address, value: Int] {
	ein._owner = sender
	value >= 0
	value <= LIMIT[] //por la limitación de la sumatoria
	ein._deposits.d[refundee].add[value] <= LIMIT[]
}

pred met_deposit[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, refundee: Address, value: Int] {
	//PRE
	pre_deposit[ein]
	pre_params_deposit[ein, sender, refundee, value]	
	
	//POST
	eout._deposits.d = ein._deposits.d++refundee->ein._deposits.d[refundee].add[value]
	eout._balance = ein._balance.add[value]

	//eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	//eout._balance = ein._balance
	eout._init = ein._init
	eout._beneficiaryWithdrawal = ein._beneficiaryWithdrawal
}


pred pre_close[ein: EstadoConcreto] {
	ein._state = Active
	ein._init = True
}

pred pre_params_close[ein: EstadoConcreto, sender:Address, refundee: Address, value: Int] {
	ein._owner = sender
}

pred met_close[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, refundee: Address, value: Int] {
	//PRE
	pre_close[ein]
	pre_params_close[ein, sender, refundee, value]
	
	
	//POST
	eout._state = Closed

	eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
	eout._beneficiaryWithdrawal = ein._beneficiaryWithdrawal
}


pred pre_enableRefunds[ein: EstadoConcreto] {
	ein._state = Active
	ein._init = True
}

pred pre_params_enableRefunds[ein: EstadoConcreto, sender:Address] {
	ein._owner = sender
}

pred met_enableRefunds[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_enableRefunds[ein]
	pre_params_enableRefunds[ein, sender]	
	
	//POST
	eout._state = Refunding

	eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	//eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
	eout._beneficiaryWithdrawal = ein._beneficiaryWithdrawal
}



pred pre_beneficiaryWithdraw[ein: EstadoConcreto] {
	ein._state = Closed
	ein._balance > 0
	ein._init = True
}

pred pre_params_beneficiaryWithdraw[ein: EstadoConcreto, sender:Address] {
}

pred met_beneficiaryWithdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_beneficiaryWithdraw[ein]
	pre_params_beneficiaryWithdraw[ein, sender]
	
	//POST
	eout._balance = 0
	eout._beneficiaryWithdrawal = True

	eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	//eout._balance = ein._balance
	eout._init = ein._init
}


pred pre_withdraw[ein: EstadoConcreto] {
	ein._state = Refunding
	ein._init = True
	some a:Address | a in (ein._deposits.d).Int and ein._deposits.d[a] > 0 //to be equal verisol
}

pred pre_params_withdraw[ein: EstadoConcreto, sender:Address, payee: Address] {
	ein._deposits.d[payee] > 0
	ein._owner = sender // to be equal verisol 
}

pred met_withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, payee: Address] {
	//PRE
	pre_withdraw[ein]
	pre_params_withdraw[ein, sender, payee]
	
	//POST
	eout._deposits.d = ein._deposits.d++payee->0
	eout._balance = ein._balance.sub[ein._deposits.d[payee]]

	//eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	//eout._balance = ein._balance
	eout._init = ein._init
	eout._beneficiaryWithdrawal = ein._beneficiaryWithdrawal
}

pred pre_transferPrimary[e: EstadoConcreto] {
	some e._state
	e._owner != Address0x0
}

pred pre_params_transferPrimary[ein: EstadoConcreto, sender:Address, recipient: Address] {
	ein._owner = sender
	recipient != Address0x0
}

pred met_transferPrimary[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, recipient: Address] {
	///PRE
	pre_transferPrimary[ein]
	pre_params_transferPrimary[ein, sender, recipient]
	
	//POST
	eout._owner = recipient

	eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	//eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
	eout._init = ein._init
	eout._beneficiaryWithdrawal = ein._beneficiaryWithdrawal
}

pred pre_t[ein: EstadoConcreto] {
	ein._init = True
}

pred pre_params_t[ein: EstadoConcreto, sender: Address, timeElapsed: Int] {
	timeElapsed >= 0
}

pred met_t[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, timeElapsed: Int] {
	//PRE
	pre_t[ein]
	pre_params_t[ein, sender, timeElapsed]

	eout._balance = ein._balance
	eout._deposits = ein._deposits
	eout._beneficiary = ein._beneficiary
	eout._owner = ein._owner
	eout._state = ein._state
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._init = ein._init
	eout._beneficiaryWithdrawal = ein._beneficiaryWithdrawal
}




//////////////////////////////////////////////////////////////////////////////////////
// I add a predicate for each possible theoretical partition //
//////////////////////////////////////////////////////////////////////////////////////

pred partitionS00[e: EstadoConcreto]{
	pre_constructor[e]
	// (invariante[e])
	// e._owner = Address0x0
	// no e._state
	// no e._deposits.d
}

pred partitionINV[e: EstadoConcreto]{
	notInvariante[e]
}

pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	e._state = Active
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	e._state = Refunding
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	e._state = Closed
}


// pred blue_transition__S00__a__S01__mediante_met_constructor {
// 	some x: EstadoConcreto | partitionS01[x] and (pre_transferPrimary[x] and (all sender:{this/Address}, recipient:{this/Address} | //pre_params_transferPrimary[x, sender, recipient] implies some y:EstadoConcreto | met_transferPrimary[x,y,sender, recipient] and not //partitionS01[y]))
// }
// run blue_transition__S00__a__S01__mediante_met_constructor for 16 EstadoConcreto, 4 Int, 2 Deposit, 2 SumatoriaSeq


// pred e_transition__S00__a__S01__mediante_met_constructor {
// 	some x, y: EstadoConcreto | partitionS01[x] and (pre_transferPrimary[x] and (some sender:{this/Address}, recipient:{this/Address} | //pre_params_transferPrimary[x, sender, recipient] and met_transferPrimary[x,y,sender, recipient] and partitionS01[y]))
// }
// run e_transition__S00__a__S01__mediante_met_constructor for 16 EstadoConcreto, 4 Int, 2 Deposit, 2 SumatoriaSeq





pred transition__S02__a__S01__mediante_met_deposit{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_deposit[x, y, v10, v11, v20])
}

pred transition__S02__a__S02__mediante_met_deposit{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_deposit[x, y, v10, v11, v20])
}

pred transition__S02__a__S03__mediante_met_deposit{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_deposit[x, y, v10, v11, v20])
}

run transition__S02__a__S01__mediante_met_deposit for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_deposit for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_deposit for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_close{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_close[x, y, v10, v11, v20])
}

pred transition__S02__a__S02__mediante_met_close{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_close[x, y, v10, v11, v20])
}

pred transition__S02__a__S03__mediante_met_close{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_close[x, y, v10, v11, v20])
}

run transition__S02__a__S01__mediante_met_close for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_close for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_close for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_enableRefunds{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_enableRefunds[x, y, v10])
}

pred transition__S02__a__S02__mediante_met_enableRefunds{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_enableRefunds[x, y, v10])
}

pred transition__S02__a__S03__mediante_met_enableRefunds{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_enableRefunds[x, y, v10])
}

run transition__S02__a__S01__mediante_met_enableRefunds for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_enableRefunds for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_enableRefunds for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_beneficiaryWithdraw{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_beneficiaryWithdraw[x, y, v10])
}

pred transition__S02__a__S02__mediante_met_beneficiaryWithdraw{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_beneficiaryWithdraw[x, y, v10])
}

pred transition__S02__a__S03__mediante_met_beneficiaryWithdraw{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_beneficiaryWithdraw[x, y, v10])
}

run transition__S02__a__S01__mediante_met_beneficiaryWithdraw for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_beneficiaryWithdraw for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_beneficiaryWithdraw for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_withdraw{
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_withdraw[x, y, v10, v11])
}

pred transition__S02__a__S02__mediante_met_withdraw{
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_withdraw[x, y, v10, v11])
}

pred transition__S02__a__S03__mediante_met_withdraw{
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_withdraw[x, y, v10, v11])
}

run transition__S02__a__S01__mediante_met_withdraw for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_withdraw for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_withdraw for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_transferPrimary{
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_transferPrimary[x, y, v10, v11])
}

pred transition__S02__a__S02__mediante_met_transferPrimary{
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_transferPrimary[x, y, v10, v11])
}

pred transition__S02__a__S03__mediante_met_transferPrimary{
	(some x,y:EstadoConcreto, v10:Address, v11:Address |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_transferPrimary[x, y, v10, v11])
}

run transition__S02__a__S01__mediante_met_transferPrimary for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_transferPrimary for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_transferPrimary for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
pred transition__S02__a__S01__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS01[y] and
		v10 != Address0x0 and met_t[x, y, v10, v20])
}

pred transition__S02__a__S02__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS02[y] and
		v10 != Address0x0 and met_t[x, y, v10, v20])
}

pred transition__S02__a__S03__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS02[x] and partitionS03[y] and
		v10 != Address0x0 and met_t[x, y, v10, v20])
}

run transition__S02__a__S01__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S02__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq
run transition__S02__a__S03__mediante_met_t for 10 EstadoConcreto, 5 Deposit, 10 SumatoriaSeq

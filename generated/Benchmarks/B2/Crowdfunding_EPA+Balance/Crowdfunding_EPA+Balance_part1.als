abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressBeneficiary extends Address{}// concrete states
abstract sig EstadoConcreto {
	_owner: Address,
	_maxBlock: Int,
	_goal: Int,
	_backers: Backer,
	_funded: Bool,
	_balance: Int,
	_blockNumber: Int, //lo agrego para simular el paso del tiempo
	_init: Bool
}

sig Backer{b: Address->lone Int}


fun LIMIT[]: Int {2}

pred invariante [e:EstadoConcreto] {
	e._init = True
	e._owner != Address0x0
	//Mientras esté en periodo de aportes, la suma de depósitos debe ser igual al balance
	//e._blockNumber <= e._maxBlock implies e._balance = sumatoria[e]
	e._blockNumber <= e._maxBlock implies sumatoria[e._backers, e._balance]
	//Si se terminó el tiempo, debe suceder que balance <= sumaDepósitos (cuando hace getFunds balance queda en cero)
	//Más especificamente, balance debe ser igual sumatoria de sumaDepósitos para k elementos (0<=k<#backers)
	e._blockNumber > e._maxBlock implies ((e._funded = True and e._balance = 0) or sumatoria[e._backers, e._balance]) //sumatoriaSubSeq[e._backers, e._balance])
	all s:SumatoriaSeq, i:Int | some s.sec[i] implies s.sec[i] >= 0
	some s:SumatoriaSeq | s.sec = 0->0
	some s:SumatoriaSeq | s.sec = 0->0+1->0
	some s:SumatoriaSeq | s.sec = 0->1
	some s:SumatoriaSeq | s.sec = 0->1+1->0
	some s:SumatoriaSeq | s.sec = 0->2
	some s:SumatoriaSeq | s.sec = 0->2+1->0
	// some s:SumatoriaSeq | s.sec = 0->3
	// some s:SumatoriaSeq | s.sec = 0->3+1->0

	//Si funded=true, entonces balance = 0
	e._funded = True implies (e._balance = 0 and e._blockNumber > e._maxBlock)

	//No Negativos
	e._balance >= 0 and e._blockNumber >= 0 and e._maxBlock >= 0 and e._goal >= 0
	all d0:Address | e._backers.b[d0] >= 0

	//fixed size: Int= 0,1,2,3; max length=4
	all d0:Address | e._backers.b[d0] >= 0 and e._backers.b[d0] <= LIMIT[]
	#(e._backers.b.Int) <= LIMIT[]
}

pred notInvariante[e: EstadoConcreto]{
	(not invariante[e])
	some sumaSeq: SumatoriaSeq, suma: Int | toSeq[e._backers, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
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

pred sumatoria [s: set Backer, suma: Int] {
	some sumaSeq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
}

pred sumatoriaSubSeq [s: set Backer, suma: Int] {
	some sumaSeq: SumatoriaSeq, subseq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and
			subSeq[sumaSeq.sec, subseq.sec] and sumof[subseq.sec] = suma
}

pred subSeq [original: seq Int, subseq: seq Int] {
	#subseq <= #original
	all i: Int | some subseq[i] implies subseq[i] in original.elems
	all i: Int | some subseq[i] implies #subseq.i <= #original.i
}

pred toSeq [s: set Backer, ret: seq Int] {
	all d0: s.b.Int | some i: Int | ret[i]=s.b[d0] //Todo elemento del set está en la seq
	all i: Int | some ret[i] implies some d0: s.b.Int | s.b[d0]=ret[i]//Todo elemento de la seq está en el set
	all i: Int | #(s.b.i) = #(ret.i) //#elem(set,e) = #elem(seq,e)
	#(s.b.Int)=#(ret)
}


sig SumatoriaSeq {sec: seq Int}

pred pre_constructor [ein: EstadoConcreto] {
	ein._init = False
	ein._owner = Address0x0
	ein._maxBlock = 0
	ein._goal = 0
	no ein._backers.b
	ein._funded = False
	ein._balance = 0
	ein._blockNumber > 0
}

pred pre_params_constructor [ein: EstadoConcreto, sender:Address, owner: Address, max_block: Int, goal: Int] {
	max_block >= 0
	goal >= 0
}

pred met_constructor [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, owner: Address, max_block: Int, goal: Int] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, owner, max_block, goal]

	//Post
	eout._owner = owner
	eout._maxBlock = max_block
	eout._goal = goal
	eout._init = True

	//out._owner = Address0x0
	//eout._maxBlock = 0
	//eout._goal = 0
	eout._backers = ein._backers
	eout._funded = False
	eout._balance = ein._balance
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
}


pred pre_donate[e: EstadoConcreto] {
	e._maxBlock > e._blockNumber //BUG
	e._init = True
}

pred pre_params_donate [ein: EstadoConcreto, sender:Address, value: Int] {
	(sender !in ein._backers.b.Int or ein._backers.b[sender] = 0)
	value >= 0
	value <= LIMIT[] //por la limitación de la sumatoria
}

pred met_donate [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int] {
	//PRE
	pre_donate[ein]
	pre_params_donate[ein, sender, value]

	//POST
	//(backers[sender] = 0) {
	eout._backers.b = ein._backers.b++sender->value
	eout._balance = ein._balance.add[value]

	eout._owner = ein._owner
	eout._maxBlock = ein._maxBlock
	eout._goal = ein._goal
	//eout._backers = ein._backers
	//eout._sumaseq = ein.sumaseq
	eout._funded = ein._funded
	//eout._balance = ein._balance
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._init = ein._init
}


pred pre_getFunds [e: EstadoConcreto] {
	e._maxBlock < e._blockNumber
	e._goal <= e._balance
	e._init = True
}

pred pre_params_getFunds [ein: EstadoConcreto, sender:Address] {
	sender = ein._owner
}

pred met_getFunds [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_getFunds[ein]
	pre_params_getFunds[ein, sender]
	
	//POST
	eout._funded = True
	eout._balance = 0

	eout._owner = ein._owner
	eout._maxBlock = ein._maxBlock
	eout._goal = ein._goal
	eout._backers = ein._backers
	//eout._funded = ein._funded
	//eout._balance = ein._balance
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._init = ein._init
}

pred pre_claim[e: EstadoConcreto] {
	e._blockNumber > e._maxBlock
	e._funded = False
	e._goal > e._balance
	some a:Address | e._backers.b[a] > 0
	e._init = True
}

pred pre_params_claim[ein: EstadoConcreto, sender:Address] {
	ein._backers.b[sender] != 0
}

pred met_claim[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//PRE
	pre_claim[ein]
	pre_params_claim[ein, sender]
	
	//POST
	(let val = ein._backers.b[sender] |
		eout._backers.b = ein._backers.b++sender->0 and 
		eout._balance = ein._balance.sub[val])

	eout._owner = ein._owner
	eout._maxBlock = ein._maxBlock
	eout._goal = ein._goal
	//eout._backers = ein._backers
	//eout._sumaseq = ein._sumaseq
	eout._funded = ein._funded
	//eout._balance = ein._balance
	eout._blockNumber = ein._blockNumber
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
	eout._maxBlock = ein._maxBlock
	eout._goal = ein._goal
	eout._backers = ein._backers
	eout._funded = ein._funded
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

pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS09[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS10[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS11[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS12[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS13[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS14[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS15[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS16[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS17[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS18[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS19[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS20[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS21[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS22[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS23[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS24[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS25[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS26[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS27[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance > 0
}

pred partitionS28[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS29[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS30[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS31[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS32[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance > 0
}

pred partitionS33[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS34[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS35[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS36[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS37[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS38[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS39[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS40[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS41[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS42[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS43[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS44[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS45[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS46[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS47[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS48[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS49[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS50[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS51[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS52[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS53[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS54[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS55[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS56[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS57[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS58[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS59[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and pre_t[e]
	e._balance = 0
}

pred partitionS60[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS61[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS62[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS63[e: EstadoConcreto]{
	(invariante[e])
	pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance = 0
}

pred partitionS64[e: EstadoConcreto]{
	(invariante[e])
	not pre_constructor [e] and not pre_donate [e] and not pre_getFunds [e] and not pre_claim[e] and not pre_t[e]
	e._balance = 0
}




pred transition__S00__a__S17__mediante_met_constructor {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int, v21:Int |
		partitionS00[x] and partitionS17[y] and
		v10 != Address0x0 and met_constructor [x, y, v10, v11, v20, v21])
}

pred transition__S00__a__S18__mediante_met_constructor {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int, v21:Int |
		partitionS00[x] and partitionS18[y] and
		v10 != Address0x0 and met_constructor [x, y, v10, v11, v20, v21])
}

pred transition__S00__a__S20__mediante_met_constructor {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int, v21:Int |
		partitionS00[x] and partitionS20[y] and
		v10 != Address0x0 and met_constructor [x, y, v10, v11, v20, v21])
}

pred transition__S00__a__S27__mediante_met_constructor {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int, v21:Int |
		partitionS00[x] and partitionS27[y] and
		v10 != Address0x0 and met_constructor [x, y, v10, v11, v20, v21])
}

pred transition__S00__a__S50__mediante_met_constructor {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int, v21:Int |
		partitionS00[x] and partitionS50[y] and
		v10 != Address0x0 and met_constructor [x, y, v10, v11, v20, v21])
}

pred transition__S00__a__S52__mediante_met_constructor {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int, v21:Int |
		partitionS00[x] and partitionS52[y] and
		v10 != Address0x0 and met_constructor [x, y, v10, v11, v20, v21])
}

pred transition__S00__a__S59__mediante_met_constructor {
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v20:Int, v21:Int |
		partitionS00[x] and partitionS59[y] and
		v10 != Address0x0 and met_constructor [x, y, v10, v11, v20, v21])
}

run transition__S00__a__S17__mediante_met_constructor  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S00__a__S18__mediante_met_constructor  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S00__a__S20__mediante_met_constructor  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S00__a__S27__mediante_met_constructor  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S00__a__S50__mediante_met_constructor  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S00__a__S52__mediante_met_constructor  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S00__a__S59__mediante_met_constructor  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
pred transition__S17__a__S17__mediante_met_donate {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS17[x] and partitionS17[y] and
		v10 != Address0x0 and met_donate [x, y, v10, v20])
}

pred transition__S17__a__S18__mediante_met_donate {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS17[x] and partitionS18[y] and
		v10 != Address0x0 and met_donate [x, y, v10, v20])
}

pred transition__S17__a__S20__mediante_met_donate {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS17[x] and partitionS20[y] and
		v10 != Address0x0 and met_donate [x, y, v10, v20])
}

pred transition__S17__a__S27__mediante_met_donate {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS17[x] and partitionS27[y] and
		v10 != Address0x0 and met_donate [x, y, v10, v20])
}

pred transition__S17__a__S50__mediante_met_donate {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS17[x] and partitionS50[y] and
		v10 != Address0x0 and met_donate [x, y, v10, v20])
}

pred transition__S17__a__S52__mediante_met_donate {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS17[x] and partitionS52[y] and
		v10 != Address0x0 and met_donate [x, y, v10, v20])
}

pred transition__S17__a__S59__mediante_met_donate {
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS17[x] and partitionS59[y] and
		v10 != Address0x0 and met_donate [x, y, v10, v20])
}

run transition__S17__a__S17__mediante_met_donate  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S18__mediante_met_donate  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S20__mediante_met_donate  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S27__mediante_met_donate  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S50__mediante_met_donate  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S52__mediante_met_donate  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S59__mediante_met_donate  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
pred transition__S17__a__S17__mediante_met_getFunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS17[y] and
		v10 != Address0x0 and met_getFunds [x, y, v10])
}

pred transition__S17__a__S18__mediante_met_getFunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS18[y] and
		v10 != Address0x0 and met_getFunds [x, y, v10])
}

pred transition__S17__a__S20__mediante_met_getFunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS20[y] and
		v10 != Address0x0 and met_getFunds [x, y, v10])
}

pred transition__S17__a__S27__mediante_met_getFunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS27[y] and
		v10 != Address0x0 and met_getFunds [x, y, v10])
}

pred transition__S17__a__S50__mediante_met_getFunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS50[y] and
		v10 != Address0x0 and met_getFunds [x, y, v10])
}

pred transition__S17__a__S52__mediante_met_getFunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS52[y] and
		v10 != Address0x0 and met_getFunds [x, y, v10])
}

pred transition__S17__a__S59__mediante_met_getFunds {
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS59[y] and
		v10 != Address0x0 and met_getFunds [x, y, v10])
}

run transition__S17__a__S17__mediante_met_getFunds  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S18__mediante_met_getFunds  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S20__mediante_met_getFunds  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S27__mediante_met_getFunds  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S50__mediante_met_getFunds  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S52__mediante_met_getFunds  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S59__mediante_met_getFunds  for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
pred transition__S17__a__S17__mediante_met_claim{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS17[y] and
		v10 != Address0x0 and met_claim[x, y, v10])
}

pred transition__S17__a__S18__mediante_met_claim{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS18[y] and
		v10 != Address0x0 and met_claim[x, y, v10])
}

pred transition__S17__a__S20__mediante_met_claim{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS20[y] and
		v10 != Address0x0 and met_claim[x, y, v10])
}

pred transition__S17__a__S27__mediante_met_claim{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS27[y] and
		v10 != Address0x0 and met_claim[x, y, v10])
}

pred transition__S17__a__S50__mediante_met_claim{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS50[y] and
		v10 != Address0x0 and met_claim[x, y, v10])
}

pred transition__S17__a__S52__mediante_met_claim{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS52[y] and
		v10 != Address0x0 and met_claim[x, y, v10])
}

pred transition__S17__a__S59__mediante_met_claim{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS59[y] and
		v10 != Address0x0 and met_claim[x, y, v10])
}

run transition__S17__a__S17__mediante_met_claim for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S18__mediante_met_claim for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S20__mediante_met_claim for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S27__mediante_met_claim for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S50__mediante_met_claim for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S52__mediante_met_claim for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S59__mediante_met_claim for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
pred transition__S17__a__S17__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS17[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S17__a__S18__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS18[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S17__a__S20__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS20[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S17__a__S27__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS27[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S17__a__S50__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS50[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S17__a__S52__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS52[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

pred transition__S17__a__S59__mediante_met_t{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS17[x] and partitionS59[y] and
		v10 != Address0x0 and met_t[x, y, v10])
}

run transition__S17__a__S17__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S18__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S20__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S27__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S50__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S52__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq
run transition__S17__a__S59__mediante_met_t for 10 EstadoConcreto, 4 Int, 5 Backer, 10 SumatoriaSeq

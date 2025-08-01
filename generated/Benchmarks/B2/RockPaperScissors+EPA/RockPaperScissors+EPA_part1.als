
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Address{}
one sig Address0x0 extends Address{}
one sig Address1 extends Address{}
one sig Address2 extends Address{}
one sig Address3 extends Address{}// concrete states
abstract sig EstadoConcreto {
	_player1: Address,
	_player2: Address,
	_owner: Address,
	_p1Choice: Int,
	_p2Choice: Int,
	_payoffMatrix: Int->Int->Int,
	_balance: Address-> lone Int,
	_init: Bool
}

pred invariante[e:EstadoConcreto] {
	e._init = True
	e._p1Choice >= -1 and e._p1Choice <= 2
	e._p2Choice >= -1 and e._p2Choice <= 2
	
	e._payoffMatrix = 0->0->0 + 0->1->2 + 0->2->1 + 1->0->1 + 1->1->0 + 1->2->2 + 2->0->2 + 2->1->1 + 2->2->0
	
	//e._owner != e._player1 and e._owner != e._player2 and e._player1 != e._player2
	some e._balance
	#e._balance = 4
	(all a:Address | e._balance[a] = 0)
	e._player1 != e._player2
	e._player1 != e._owner
	e._player2 != e._owner
	e._player1 != Address0x0
	e._player2 != Address0x0
	e._owner != Address0x0
}

pred pre_constructor[ein: EstadoConcreto] {
	ein._p1Choice = -1
	ein._p2Choice = -1
	ein._init = False
}

pred pre_params_constructor[ein: EstadoConcreto, player1: Address, player2: Address, owner: Address] {
	player1 != Address0x0
	player2 != Address0x0
	owner != Address0x0
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, player1: Address, player2: Address, owner: Address] {
	//PRE
	pre_constructor[ein]
	pre_params_constructor[ein, player1, player2, owner]

	//POST
	eout._player1 = player1
	eout._player2 = player2
	eout._owner = owner
	eout._init = True

	//Rock - 0
	//Paper - 1
	//Scissors - 2
	eout._payoffMatrix = ein._payoffMatrix
	// eout._payoffMatrix = ein._payoffMatrix++0->0->0
	// eout._payoffMatrix = ein._payoffMatrix++0->1->2
	// eout._payoffMatrix = ein._payoffMatrix++0->2->1
	// eout._payoffMatrix = ein._payoffMatrix++1->0->1
	// eout._payoffMatrix = ein._payoffMatrix++1->1->0
	// eout._payoffMatrix = ein._payoffMatrix++1->2->2
	// eout._payoffMatrix = ein._payoffMatrix++2->0->2
	// eout._payoffMatrix = ein._payoffMatrix++2->1->1
	// eout._payoffMatrix = ein._payoffMatrix++2->2->0

	eout._p1Choice = ein._p1Choice
	eout._p2Choice = ein._p2Choice
	//eout._player1 = ein._player1
	//eout._player2 = ein._player2
	//eout._owner = ein._owner
	//eout._payoffMatrix = ein._payoffMatrix
	eout._balance = ein._balance
}

pred pre_choicePlayer1[e: EstadoConcreto] {
	e._p1Choice = -1
	e._init = True
}

pred pre_params_choicePlayer1[ein: EstadoConcreto, sender: Address, choice: Int, value: Int] {
	sender = ein._player1
	sender != Address0x0
	choice >= 0 and choice <= 2
}

pred met_choicePlayer1[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, choice: Int, value: Int] {
	//PRE
	pre_choicePlayer1[ein]
	pre_params_choicePlayer1[ein, sender, choice, value]


	//POST
	eout._p1Choice = choice
	eout._balance = ein._balance++Address0x0->ein._balance[Address0x0].add[value]

	//eout._p1Choice = ein._p1Choice
	eout._p2Choice = ein._p2Choice
	eout._player1 = ein._player1
	eout._player2 = ein._player2
	eout._owner = ein._owner
	eout._payoffMatrix = ein._payoffMatrix
	eout._init = ein._init
	//eout._balance = ein._balance
}

pred pre_choicePlayer2[e: EstadoConcreto] {
	e._p2Choice = -1
	e._init = True
}

pred pre_params_choicePlayer2[ein: EstadoConcreto, sender: Address, choice: Int, value: Int] {
	sender = ein._player2
	sender != Address0x0
	choice >= 0 and choice <= 2
}

pred met_choicePlayer2[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, choice: Int, value: Int] {
	//PRE
	pre_choicePlayer2[ein]
	pre_params_choicePlayer2[ein, sender, choice, value]


	//POST
	eout._p2Choice = choice
	eout._balance = ein._balance++Address0x0->ein._balance[Address0x0].add[value]

	eout._p1Choice = ein._p1Choice
	//eout._p2Choice = ein._p2Choice
	eout._player1 = ein._player1
	eout._player2 = ein._player2
	eout._owner = ein._owner
	eout._payoffMatrix = ein._payoffMatrix
	// eout._balance = ein._balance
	eout._init = ein._init
}

pred pre_determineWinner[e:EstadoConcreto] {
	e._p1Choice != -1 and e._p2Choice != -1
	e._init = True
}

pred pre_params_determineWinner[ein: EstadoConcreto, sender: Address] {
}

pred met_determineWinner[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_determineWinner[ein]
	pre_params_determineWinner[ein, sender]
	
	//POST
	(let winner = (ein._payoffMatrix[ein._p1Choice])[ein._p2Choice] |
			(winner = 1) => eout._balance = ein._balance++Address1->ein._balance[Address0x0]
		else
			(winner = 2) => eout._balance = ein._balance++Address2->ein._balance[Address0x0]
            	else
			(winner = 0) => eout._balance = ein._balance++ein._owner->ein._balance[Address0x0]
	)

	eout._balance = ein._balance++Address0x0->0

	eout._p1Choice = ein._p1Choice
	eout._p2Choice = ein._p2Choice
	eout._player1 = ein._player1
	eout._player2 = ein._player2
	eout._owner = ein._owner
	eout._payoffMatrix = ein._payoffMatrix
	// eout._balance = ein._balance
	eout._init = ein._init
}

pred isWinner[user: Address, e:EstadoConcreto] {
	(let winner = (e._payoffMatrix[e._p1Choice])[e._p2Choice] |
			(winner = 1) => user = e._player1
		else
			(winner = 2) => user = e._player2
            	else
			(winner = 0) => user = e._owner
	)
}

//////////////////////////////////////////////////////////////////////////////////////
// I add a predicate for each possible theoretical partition //
//////////////////////////////////////////////////////////////////////////////////////
pred partitionS00[e: EstadoConcreto]{
	pre_constructor[e]
}


pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_choicePlayer1[e] and pre_choicePlayer2[e] and pre_determineWinner[e]
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	not pre_choicePlayer1[e] and pre_choicePlayer2[e] and pre_determineWinner[e]
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_choicePlayer1[e] and not pre_choicePlayer2[e] and pre_determineWinner[e]
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	pre_choicePlayer1[e] and pre_choicePlayer2[e] and not pre_determineWinner[e]
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	not pre_choicePlayer1[e] and not pre_choicePlayer2[e] and pre_determineWinner[e]
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	not pre_choicePlayer1[e] and pre_choicePlayer2[e] and not pre_determineWinner[e]
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	pre_choicePlayer1[e] and not pre_choicePlayer2[e] and not pre_determineWinner[e]
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	not pre_choicePlayer1[e] and not pre_choicePlayer2[e] and not pre_determineWinner[e]
}




pred transition__S00__a__S04__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v12:Address |
		partitionS00[x] and partitionS04[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v12])
}

pred transition__S00__a__S05__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v12:Address |
		partitionS00[x] and partitionS05[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v12])
}

pred transition__S00__a__S06__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v12:Address |
		partitionS00[x] and partitionS06[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v12])
}

pred transition__S00__a__S07__mediante_met_constructor{
	(some x,y:EstadoConcreto, v10:Address, v11:Address, v12:Address |
		partitionS00[x] and partitionS07[y] and
		v10 != Address0x0 and met_constructor[x, y, v10, v11, v12])
}

run transition__S00__a__S04__mediante_met_constructor for 10 EstadoConcreto
run transition__S00__a__S05__mediante_met_constructor for 10 EstadoConcreto
run transition__S00__a__S06__mediante_met_constructor for 10 EstadoConcreto
run transition__S00__a__S07__mediante_met_constructor for 10 EstadoConcreto
pred transition__S04__a__S04__mediante_met_choicePlayer1{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int |
		partitionS04[x] and partitionS04[y] and
		v10 != Address0x0 and met_choicePlayer1[x, y, v10, v20, v21])
}

pred transition__S04__a__S05__mediante_met_choicePlayer1{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int |
		partitionS04[x] and partitionS05[y] and
		v10 != Address0x0 and met_choicePlayer1[x, y, v10, v20, v21])
}

pred transition__S04__a__S06__mediante_met_choicePlayer1{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int |
		partitionS04[x] and partitionS06[y] and
		v10 != Address0x0 and met_choicePlayer1[x, y, v10, v20, v21])
}

pred transition__S04__a__S07__mediante_met_choicePlayer1{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int |
		partitionS04[x] and partitionS07[y] and
		v10 != Address0x0 and met_choicePlayer1[x, y, v10, v20, v21])
}

run transition__S04__a__S04__mediante_met_choicePlayer1 for 10 EstadoConcreto
run transition__S04__a__S05__mediante_met_choicePlayer1 for 10 EstadoConcreto
run transition__S04__a__S06__mediante_met_choicePlayer1 for 10 EstadoConcreto
run transition__S04__a__S07__mediante_met_choicePlayer1 for 10 EstadoConcreto
pred transition__S04__a__S04__mediante_met_choicePlayer2{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int |
		partitionS04[x] and partitionS04[y] and
		v10 != Address0x0 and met_choicePlayer2[x, y, v10, v20, v21])
}

pred transition__S04__a__S05__mediante_met_choicePlayer2{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int |
		partitionS04[x] and partitionS05[y] and
		v10 != Address0x0 and met_choicePlayer2[x, y, v10, v20, v21])
}

pred transition__S04__a__S06__mediante_met_choicePlayer2{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int |
		partitionS04[x] and partitionS06[y] and
		v10 != Address0x0 and met_choicePlayer2[x, y, v10, v20, v21])
}

pred transition__S04__a__S07__mediante_met_choicePlayer2{
	(some x,y:EstadoConcreto, v10:Address, v20:Int, v21:Int |
		partitionS04[x] and partitionS07[y] and
		v10 != Address0x0 and met_choicePlayer2[x, y, v10, v20, v21])
}

run transition__S04__a__S04__mediante_met_choicePlayer2 for 10 EstadoConcreto
run transition__S04__a__S05__mediante_met_choicePlayer2 for 10 EstadoConcreto
run transition__S04__a__S06__mediante_met_choicePlayer2 for 10 EstadoConcreto
run transition__S04__a__S07__mediante_met_choicePlayer2 for 10 EstadoConcreto
pred transition__S04__a__S04__mediante_met_determineWinner{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS04[x] and partitionS04[y] and
		v10 != Address0x0 and met_determineWinner[x, y, v10])
}

pred transition__S04__a__S05__mediante_met_determineWinner{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS04[x] and partitionS05[y] and
		v10 != Address0x0 and met_determineWinner[x, y, v10])
}

pred transition__S04__a__S06__mediante_met_determineWinner{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS04[x] and partitionS06[y] and
		v10 != Address0x0 and met_determineWinner[x, y, v10])
}

pred transition__S04__a__S07__mediante_met_determineWinner{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS04[x] and partitionS07[y] and
		v10 != Address0x0 and met_determineWinner[x, y, v10])
}

run transition__S04__a__S04__mediante_met_determineWinner for 10 EstadoConcreto
run transition__S04__a__S05__mediante_met_determineWinner for 10 EstadoConcreto
run transition__S04__a__S06__mediante_met_determineWinner for 10 EstadoConcreto
run transition__S04__a__S07__mediante_met_determineWinner for 10 EstadoConcreto

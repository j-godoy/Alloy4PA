abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressC extends Address{}
one sig AddressD extends Address{}
one sig AddressE extends Address{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig EstadoContrato{}
one sig Created extends EstadoContrato{}
one sig InUse extends EstadoContrato{}

abstract sig Mode{}
one sig Off extends Mode{}
one sig Cool extends Mode{}
one sig Heat extends Mode{}
one sig Auto extends Mode{}

abstract sig EstadoConcreto {
	_installer: Address,
	_user: Address,
	_targetTemperature: Int,
	_mode: lone Mode,
	_state: lone EstadoContrato,
	_init : Bool
}


pred invariante[e:EstadoConcreto] {
	e._init = True
}

pred pre_constructor[ein: EstadoConcreto] {
	ein._init = False
	ein._installer = Address0x0
	ein._user = Address0x0
	ein._targetTemperature = 0
	no ein._mode
	no ein._state
}

pred pre_params_constructor[ein: EstadoConcreto, sender:Address, thermostatInstaller: Address, thermostatUser:Address] {

}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, thermostatInstaller: Address, thermostatUser:Address] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, thermostatInstaller, thermostatUser]
	
	//Post
	eout._installer = thermostatInstaller
	eout._user = thermostatUser
	eout._targetTemperature = 4
	eout._state = Created
	eout._init = True

	//eout._installer = ein._installer
	//eout._user = ein._user
	//eout._targetTemperature = ein._targetTemperature
	eout._mode = ein._mode
	//eout._state = ein._state
}

pred pre_startThermostat[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state = Created
}

pred pre_params_startThermostat[ein: EstadoConcreto, sender: Address] {
	ein._installer = sender
}

pred met_startThermostat[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_startThermostat[ein]
	pre_params_startThermostat[ein, sender]

	//Post
	eout._state = InUse

	eout._installer = ein._installer
	eout._user = ein._user
	eout._targetTemperature = ein._targetTemperature
	eout._mode = ein._mode
	eout._init = ein._init
}

pred pre_setTargetTemperature[ein: EstadoConcreto] {
	some ein._state
	ein._state = InUse
}

pred pre_params_setTargetTemperature[ein: EstadoConcreto, sender: Address, targetTemperature: Int] {
	ein._user = sender
}

pred met_setTargetTemperature[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, targetTemperature: Int] {
	//Pre
	pre_setTargetTemperature[ein]
	pre_params_setTargetTemperature[ein, sender, targetTemperature]

	//Post
	eout._targetTemperature = targetTemperature

	eout._installer = ein._installer
	eout._user = ein._user
	//eout._targetTemperature = ein._targetTemperature
	eout._mode = ein._mode
	eout._state = ein._state
	eout._init = ein._init
}

pred pre_setMode[ein: EstadoConcreto] {
	some ein._state
	ein._state = InUse
}

pred pre_params_setMode[ein: EstadoConcreto, sender: Address, mode: Mode] {
	ein._user = sender
}

pred met_setMode[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, mode: Mode] {
	//Pre	
	pre_setMode[ein]
	pre_params_setMode[ein, sender, mode]

	//Post
	eout._mode = mode

	eout._installer = ein._installer
	eout._user = ein._user
	eout._targetTemperature = ein._targetTemperature
	//eout._mode = ein._mode
	eout._state = ein._state
	eout._init = ein._init
}


// I add a predicate for each possible theoretical partition
pred partitionS00[e: EstadoConcreto]{ // 
	pre_constructor[e]
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Created
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = InUse
}





pred transition__S01__a__S01__mediante_met_startThermostat{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_startThermostat[x, y, v10])
}

pred transition__S01__a__S02__mediante_met_startThermostat{
	(some x,y:EstadoConcreto, v10:Address |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_startThermostat[x, y, v10])
}

run transition__S01__a__S01__mediante_met_startThermostat for 10 EstadoConcreto
run transition__S01__a__S02__mediante_met_startThermostat for 10 EstadoConcreto
pred transition__S01__a__S01__mediante_met_setTargetTemperature{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_setTargetTemperature[x, y, v10, v20])
}

pred transition__S01__a__S02__mediante_met_setTargetTemperature{
	(some x,y:EstadoConcreto, v10:Address, v20:Int |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_setTargetTemperature[x, y, v10, v20])
}

run transition__S01__a__S01__mediante_met_setTargetTemperature for 10 EstadoConcreto
run transition__S01__a__S02__mediante_met_setTargetTemperature for 10 EstadoConcreto
pred transition__S01__a__S01__mediante_met_setMode{
	(some x,y:EstadoConcreto, v10:Address, v20:Mode |
		partitionS01[x] and partitionS01[y] and
		v10 != Address0x0 and met_setMode[x, y, v10, v20])
}

pred transition__S01__a__S02__mediante_met_setMode{
	(some x,y:EstadoConcreto, v10:Address, v20:Mode |
		partitionS01[x] and partitionS02[y] and
		v10 != Address0x0 and met_setMode[x, y, v10, v20])
}

run transition__S01__a__S01__mediante_met_setMode for 10 EstadoConcreto
run transition__S01__a__S02__mediante_met_setMode for 10 EstadoConcreto

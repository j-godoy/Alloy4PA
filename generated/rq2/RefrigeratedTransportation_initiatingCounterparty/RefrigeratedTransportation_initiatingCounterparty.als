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

abstract sig Texto{}
one sig TextoA extends Texto{}
one sig TextoB extends Texto{}
one sig TextoC extends Texto{}
one sig TextoD extends Texto{}

abstract sig EstadoContrato{}
one sig Created extends EstadoContrato{}
one sig InTransit extends EstadoContrato{}
one sig Completed extends EstadoContrato{}
one sig OutOfCompliance extends EstadoContrato{}

abstract sig SensorType{}
one sig None extends SensorType{}
one sig Humidity extends SensorType{}
one sig Temperature extends SensorType{}

abstract sig EstadoConcreto {
	_owner: Address,
	_initiatingCounterparty: Address,
	_counterparty: Address,
	_previousCounterparty: Address,
	_device: Address,
	_supplyChainOwner: Address,
	_supplyChainObserver: Address,
	_minHumidity: Int,
	_maxHumidity: Int,
	_minTemperature: Int,
	_maxTemperature: Int,
	_complianceSensorType: SensorType,
	_complianceSensorReading: Int,
	_complianceStatus: Bool,
	_complianceDetail: Texto,
	_lastSensorUpdateTimestamp: Int,
	_state: lone EstadoContrato,
	_init: Bool
}


pred invariante[e:EstadoConcreto] {
	e._init = True
	e._state = Created implies e._initiatingCounterparty = e._counterparty
}

pred pre_constructor[ein: EstadoConcreto] {
	ein._init = False
	no ein._state
}

pred pre_params_constructor[ein: EstadoConcreto, sender: Address, device: Address, supplyChainOwner: Address,
		supplyChainObserver: Address, minHumidity: Int, maxHumidity: Int, minTemperature: Int, maxTemperature: Int] {
		minHumidity >= 0
		maxHumidity >= 0
		minTemperature >= 0
		maxTemperature >= 0
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, device: Address, supplyChainOwner: Address,
		supplyChainObserver: Address, minHumidity: Int, maxHumidity: Int, minTemperature: Int, maxTemperature: Int] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, device, supplyChainOwner, supplyChainObserver, minHumidity, maxHumidity, minTemperature, maxTemperature]

	//Post
	eout._init = True
	eout._complianceStatus = True
	eout._complianceSensorReading = -1
	eout._initiatingCounterparty = sender
	eout._owner = eout._initiatingCounterparty
	eout._counterparty = eout._initiatingCounterparty
	eout._device = device
	eout._supplyChainOwner = supplyChainOwner
	eout._supplyChainObserver = supplyChainObserver
	eout._minHumidity = minHumidity
	eout._maxHumidity = maxHumidity
	eout._minTemperature = minTemperature
	eout._maxTemperature = maxTemperature
	eout._state = Created
	eout._complianceDetail = TextoA
	eout._previousCounterparty = ein._previousCounterparty
	eout._complianceSensorType = ein._complianceSensorType
	eout._lastSensorUpdateTimestamp = ein._lastSensorUpdateTimestamp
}

pred pre_ingestTelemetry[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state != Completed
	ein._state != OutOfCompliance
}

pred pre_params_ingestTelemetry[ein: EstadoConcreto, sender:Address, humidity: Int, temperature: Int, timestamp: Int] {
	ein._device = sender
	humidity >= 0
	temperature >= 0
	timestamp >= 0
}

pred met_ingestTelemetry[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, humidity: Int, temperature: Int, timestamp: Int] {
	//Pre
	pre_ingestTelemetry[ein]
	pre_params_ingestTelemetry[ein, sender, humidity, temperature, timestamp]

	//Post
	eout._lastSensorUpdateTimestamp = timestamp
        (humidity > ein._maxHumidity or humidity < ein._minHumidity) =>
		(
	            eout._complianceSensorType = Humidity and 
	            eout._complianceSensorReading = humidity and
	            eout._complianceDetail = TextoB and 
	            eout._complianceStatus = False
		)
	else
		(
			(temperature > ein._maxTemperature or temperature < ein._minTemperature)
				=> (
						eout._complianceSensorType = Temperature and
					         eout._complianceSensorReading = temperature and
					         eout._complianceDetail = TextoC and
					         eout._complianceStatus = False
				     )
				else  (
						eout._complianceSensorType = ein._complianceSensorType and
					         eout._complianceSensorReading = ein._complianceSensorReading and
					         eout._complianceDetail = ein._complianceDetail and
					         eout._complianceStatus = ein._complianceStatus
					)
		)

	(ein._complianceStatus = False) => (eout._state = OutOfCompliance) else eout._state = ein._state
	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._owner = ein._owner
	eout._counterparty = ein._counterparty
	eout._device = ein._device
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
	eout._minHumidity = ein._minHumidity
	eout._maxHumidity = ein._maxHumidity
	eout._minTemperature = ein._minTemperature
	eout._maxTemperature = ein._maxTemperature
	eout._previousCounterparty = ein._previousCounterparty
	eout._init = ein._init
}

pred pre_transferResponsibility[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state != Completed
	ein._state != OutOfCompliance	
}

pred pre_params_transferResponsibility[ein: EstadoConcreto, sender:Address, newCounterparty: Address] {
	ein._initiatingCounterparty = sender or ein._counterparty = sender
	newCounterparty != ein._device
}

pred met_transferResponsibility[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, newCounterparty: Address] {
	//Pre
	pre_transferResponsibility[ein]
	pre_params_transferResponsibility[ein, sender, newCounterparty]

	//Post
	ein._state = Created => eout._state = InTransit else eout._state = ein._state
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = newCounterparty

	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._owner = ein._owner
	eout._device = ein._device
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
	eout._minHumidity = ein._minHumidity
	eout._maxHumidity = ein._maxHumidity
	eout._minTemperature = ein._minTemperature
	eout._maxTemperature = ein._maxTemperature
	eout._complianceSensorType = ein._complianceSensorType
	eout._complianceSensorReading = ein._complianceSensorReading
	eout._complianceDetail = ein._complianceDetail
	eout._complianceStatus = ein._complianceStatus
	eout._lastSensorUpdateTimestamp = ein._lastSensorUpdateTimestamp
	eout._init = ein._init
}

pred pre_complete[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state != Completed
	ein._state != OutOfCompliance
	ein._state != Created //agrego FIX
}

pred pre_params_complete[ein: EstadoConcreto, sender:Address] {
	ein._owner = sender or ein._supplyChainOwner = sender
}

pred met_complete[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_complete[ein]
	pre_params_complete[ein, sender]

	//Post
	eout._state = Completed
	eout._previousCounterparty = ein._counterparty
	eout._counterparty = Address0x0

	eout._initiatingCounterparty = ein._initiatingCounterparty
	eout._owner = ein._owner
	eout._device = ein._device
	eout._supplyChainOwner = ein._supplyChainOwner
	eout._supplyChainObserver = ein._supplyChainObserver
	eout._minHumidity = ein._minHumidity
	eout._maxHumidity = ein._maxHumidity
	eout._minTemperature = ein._minTemperature
	eout._maxTemperature = ein._maxTemperature
	eout._complianceSensorType = ein._complianceSensorType
	eout._complianceSensorReading = ein._complianceSensorReading
	eout._complianceDetail = ein._complianceDetail
	eout._complianceStatus = ein._complianceStatus
	eout._lastSensorUpdateTimestamp = ein._lastSensorUpdateTimestamp
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
	e._state = InTransit
}

pred partitionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Completed
}

pred partitionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = OutOfCompliance
}

pred partitionINV[e: EstadoConcreto]{ // 
	not (invariante[e])
}


// add a predicate for each possible transition
/*
From S0 to S1 with action
*/



//======predicates for blue queries======



pred blue_transition__S01__a__S02__mediante_met_transferResponsibility {
	some x: EstadoConcreto | partitionS01[x] and (not pre_transferResponsibility[x] or (all newCounterparty:{this/Address} | pre_params_transferResponsibility[x,x._initiatingCounterparty, newCounterparty] implies some y:EstadoConcreto | met_transferResponsibility[x,y,x._initiatingCounterparty, newCounterparty] and not partitionS02[y]))
}
run blue_transition__S01__a__S02__mediante_met_transferResponsibility for 10 EstadoConcreto

pred blue_transition__S00__a__S01__mediante_met_constructor {
	some x: EstadoConcreto | partitionS00[x] and ((all device:{this/Address}, supplyChainOwner:{this/Address}, supplyChainObserver:{this/Address}, minHumidity:{Int}, maxHumidity:{Int}, minTemperature:{Int}, maxTemperature:{Int} | pre_params_constructor[x,x._initiatingCounterparty, device, supplyChainOwner, supplyChainObserver, minHumidity, maxHumidity, minTemperature, maxTemperature] implies some y:EstadoConcreto | met_constructor[x,y,x._initiatingCounterparty, device, supplyChainOwner, supplyChainObserver, minHumidity, maxHumidity, minTemperature, maxTemperature] and not partitionS01[y]))
}
run blue_transition__S00__a__S01__mediante_met_constructor for 10 EstadoConcreto

pred blue_transition__S02__a__S02__mediante_met_ingestTelemetry {
	some x: EstadoConcreto | partitionS02[x] and (not pre_ingestTelemetry[x] or (all humidity:{Int}, temperature:{Int}, timestamp:{Int} | pre_params_ingestTelemetry[x,x._initiatingCounterparty, humidity, temperature, timestamp] implies some y:EstadoConcreto | met_ingestTelemetry[x,y,x._initiatingCounterparty, humidity, temperature, timestamp] and not partitionS02[y]))
}
run blue_transition__S02__a__S02__mediante_met_ingestTelemetry for 10 EstadoConcreto

pred blue_transition__S02__a__S04__mediante_met_ingestTelemetry {
	some x: EstadoConcreto | partitionS02[x] and (not pre_ingestTelemetry[x] or (all humidity:{Int}, temperature:{Int}, timestamp:{Int} | pre_params_ingestTelemetry[x,x._initiatingCounterparty, humidity, temperature, timestamp] implies some y:EstadoConcreto | met_ingestTelemetry[x,y,x._initiatingCounterparty, humidity, temperature, timestamp] and not partitionS04[y]))
}
run blue_transition__S02__a__S04__mediante_met_ingestTelemetry for 10 EstadoConcreto

pred blue_transition__S01__a__S01__mediante_met_ingestTelemetry {
	some x: EstadoConcreto | partitionS01[x] and (not pre_ingestTelemetry[x] or (all humidity:{Int}, temperature:{Int}, timestamp:{Int} | pre_params_ingestTelemetry[x,x._initiatingCounterparty, humidity, temperature, timestamp] implies some y:EstadoConcreto | met_ingestTelemetry[x,y,x._initiatingCounterparty, humidity, temperature, timestamp] and not partitionS01[y]))
}
run blue_transition__S01__a__S01__mediante_met_ingestTelemetry for 10 EstadoConcreto

pred blue_transition__S01__a__S04__mediante_met_ingestTelemetry {
	some x: EstadoConcreto | partitionS01[x] and (not pre_ingestTelemetry[x] or (all humidity:{Int}, temperature:{Int}, timestamp:{Int} | pre_params_ingestTelemetry[x,x._initiatingCounterparty, humidity, temperature, timestamp] implies some y:EstadoConcreto | met_ingestTelemetry[x,y,x._initiatingCounterparty, humidity, temperature, timestamp] and not partitionS04[y]))
}
run blue_transition__S01__a__S04__mediante_met_ingestTelemetry for 10 EstadoConcreto

pred blue_transition__S02__a__S03__mediante_met_complete {
	some x: EstadoConcreto | partitionS02[x] and (not pre_complete[x] or (pre_params_complete[x,x._initiatingCounterparty] implies some y:EstadoConcreto | met_complete[x,y,x._initiatingCounterparty] and not partitionS03[y]))
}
run blue_transition__S02__a__S03__mediante_met_complete for 10 EstadoConcreto

pred blue_transition__S02__a__S02__mediante_met_transferResponsibility {
	some x: EstadoConcreto | partitionS02[x] and (not pre_transferResponsibility[x] or (all newCounterparty:{this/Address} | pre_params_transferResponsibility[x,x._initiatingCounterparty, newCounterparty] implies some y:EstadoConcreto | met_transferResponsibility[x,y,x._initiatingCounterparty, newCounterparty] and not partitionS02[y]))
}
run blue_transition__S02__a__S02__mediante_met_transferResponsibility for 10 EstadoConcreto




//======predicates for turquoise queries======




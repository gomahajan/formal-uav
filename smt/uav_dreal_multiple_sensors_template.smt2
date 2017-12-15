(set-logic QF_NRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)

(declare-fun sensor1_bi () Real)
(declare-fun sensor1_b0 () Real)
(declare-fun sensor1_b1 () Real)
(declare-fun sensor1_b2 () Real)
(declare-fun sensor1_b3 () Real)

(declare-fun sensor2_bi () Real)
(declare-fun sensor2_b0 () Real)
(declare-fun sensor2_b1 () Real)
(declare-fun sensor2_b2 () Real)
(declare-fun sensor2_b3 () Real)

(declare-fun sensor1_qi () Real)
(declare-fun sensor1_q0 () Real)
(declare-fun sensor1_q1 () Real)
(declare-fun sensor1_q2 () Real)
(declare-fun sensor1_q3 () Real)

(declare-fun sensor2_qi () Real)
(declare-fun sensor2_q0 () Real)
(declare-fun sensor2_q1 () Real)
(declare-fun sensor2_q2 () Real)
(declare-fun sensor2_q3 () Real)

(declare-fun t0 () Real)
(declare-fun t1 () Real)
(declare-fun t2 () Real)
(declare-fun t3 () Real)

;parameters
(declare-fun p0 () Real)
(declare-fun p1 () Real)
(declare-fun p2 () Real)
(declare-fun p3 () Real)
(declare-fun p4 () Real)

(declare-fun sensor_choice_1 () Real)

;constants
(declare-fun battery_charging_rate () Real)
(declare-fun battery_discharge_rate_fly () Real)
(declare-fun battery_discharge_rate_hover () Real)
(declare-fun queue_data_rate () Real)
(declare-fun queue_upload_rate () Real)
(declare-fun drone_velocity () Real)
(declare-fun sensor1_location () Real)
(declare-fun sensor2_location () Real)

(assert(= drone_velocity 10))
(assert(= battery_charging_rate 50))
(assert(= battery_discharge_rate_fly 1))
(assert(= battery_discharge_rate_hover 1))
(assert(= queue_data_rate 1))
(assert(= queue_upload_rate 1))
(assert(= sensor1_location 10))
(assert(= sensor2_location 100))


(assert(>= t0 0))
(assert(>= t1 0))
(assert(>= t2 0))
(assert(>= t3 0))
(assert (<= bi 100))
(assert (>= bi 0))
(assert (<= b0 100))
(assert (<= b1 100))
(assert (<= b2 100))
(assert (<= b3 100))
(assert (>= qi 0))
(assert (<= qi 100))
(assert (>= q0 0))
(assert (>= q1 0))
(assert (>= q2 0))
(assert (>= q3 0))
(assert (<= x0 10))
(assert (<= x1 10))
(assert (<= x2 10))
(assert (<= x3 10))
(assert (>= x0 0))
(assert (>= x1 0))
(assert (>= x2 0))
(assert (>= x3 0))

;template
parametervalues
;sample (assert (= p0 1))
;sample (assert (= p1 1))
;sample (assert (= p2 1))
;sample (assert (= p3 1))

;charging
(assert(= x0 0))
(assert(= b0 (+ bi (* battery_charging_rate t0))))
(assert(= q0 (+ qi (* queue_data_rate t0))))
;program: choice charge when !(battery >= p2)
;program: choice sensor1 when (sensorQ >= p4)
;program: choice sensor2 when (sensorQ >= p5)
;Decides b0, sensor_choice_1
(assert (=> (>= bi p2) (= b0 bi)))
(assert (or (=> (< bi p2) (= b0 p2)) (= q0 100)))


;flying to sensor_choice_1
(assert(=> (= sensor_choice_1 1) (= x1 sensor1_location)))
(assert(=> (= sensor_choice_1 2) (= x1 sensor2_location)))
(assert(= x1 (+ x0 (* drone_velocity t1))))
(assert(= b1 (- b0 (* battery_discharge_rate_fly t1))))
(assert(= sensor1_q1 (+ sensor1_q0 (* queue_data_rate t1))))
(assert(= sensor2_q1 (+ sensor2_q0 (* queue_data_rate t1))))

;emptying queue based on sensor choice
(assert(=> (= sensor_choice_1 1) (= x2 sensor1_location)))
(assert(=> (= sensor_choice_1 2) (= x2 sensor2_location)))
;empty queue for choice
;fill other queue
(assert(= q2 (- q1 (* queue_upload_rate t2))))
(assert(= b2 (- b1 (* battery_discharge_rate_hover t2))))
;program: choice charger: empty queue till battery <= p3
;program: choice sensor2: empty queue till battery <= p6
;decides b2, choice_2
(assert (or (=> (> b1 p3) (= b2 p3)) (= q2 0)))
(assert (=> (<= b1 p3) (= b2 b1)))


;flying back or sensor2
(assert(=> (= choice_2 1) (= x3 charging_location)))
(assert(=> (= choice_2 2) (= x3 sensor2_location)))
(assert(= x3 (- x2 (* drone_velocity t3))))
(assert(= q3 (+ q2 (* queue_data_rate t3))))
(assert(= b3 (- b2 (* battery_discharge_rate_fly t3))))

;partial goal
; if choice was flying back, check invariant
;(assert(=> (= choice_2 1) (Invariant)))

;if choice2_sensor2, find b4,q4,x4
(assert(= q4 (- q3 (* queue_upload_rate t2))))
(assert(= b4 (- b3 (* battery_discharge_rate_hover t2))))
;program: choice charger: empty queue till battery <= p7
;decides b4
(assert (or (=> (> b4 p7) (= b4 p7)) (= q4 0)))
(assert (=> (<= b4 p7) (= b4 b3)))

;if choice2_sensor2, fly back
(assert(= x3 (- x2 (* drone_velocity t3))))
(assert(= q3 (+ q2 (* queue_data_rate t3))))
(assert(= b3 (- b2 (* battery_discharge_rate_fly t3))))

;partial goal
;if choice_2 was sensor2,
;(assert(=> (= choice_2 2) (Invariant)))
;goal
;Question: Does there exist starting battery,queue values such that safety is not maintained
; that is not (invariant => safety)
(assert (and (>= bi p0) (<= qi p1)))
(assert (or (<= b0 0) (<= b1 0) (<= b2 0) (<= b3 0) (>= q0 100) (>= q1 100) (>= q2 100) (>= q3 100) (not (and (>= b3 p0) (<= q3 p1)))))
(check-sat)
(exit)

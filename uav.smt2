(set-logic QF_NRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)

(declare-fun bi () Real)
(declare-fun b0 () Real)
(declare-fun b1 () Real)
(declare-fun b2 () Real)
(declare-fun b3 () Real)

(declare-fun qi () Real)
(declare-fun q0 () Real)
(declare-fun q1 () Real)
(declare-fun q2 () Real)
(declare-fun q3 () Real)

(declare-fun t0 () Real)
(declare-fun t1 () Real)
(declare-fun t2 () Real)
(declare-fun t3 () Real)

;space constraint
(define-fun constraint((b Real) (q Real)) Bool
	(and (= b 100) (= q 0))) 

;constants
(declare-fun battery_charging_rate () Real)
(declare-fun battery_discharge_rate () Real)
(declare-fun queue_data_rate () Real)
(declare-fun queue_upload_rate () Real)
(declare-fun drone_velocity () Real)

(assert(= battery_charging_rate 50))
(assert(= battery_discharge_rate 1))
(assert(= queue_data_rate 1))
(assert(= queue_upload_rate 1))
(assert(= drone_velocity 10))

(assert(>= t0 0))
(assert(>= t1 0))
(assert(>= t2 0))
(assert(>= t3 0))

(assert (constraint bi qi))

;charging
(assert(= x0 0))
(assert(= b0 (+ bi (* battery_charging_rate t0))))
(assert(= q0 (+ qi (* queue_data_rate t0))))
;program: 90<= b0 <=100
(assert(<= 90 b0))
(assert(>= 100 b0)) 

;flying to D
(assert(= x1 10))
(assert(= x1 (+ x0 (* drone_velocity t1))))
(assert(= b1 (- b0 (* battery_discharge_rate t1))))
(assert(= q1 (+ q0 (* queue_data_rate t1))))

;emptying queue
(assert(= x2 10))
(assert(= q2 (- q1 (* queue_upload_rate t2))))
(assert(= b2 (- b1 (* battery_discharge_rate t2))))
;program: 0<= q2 <=20
(assert(<= 0 q2))
(assert(>= 20 q2))

;flying back
(assert(= x3 0))
(assert(= x3 (- x2 (* drone_velocity t3))))
(assert(= q3 (+ q2 (* queue_data_rate t3))))
(assert(= b3 (- b2 (* battery_discharge_rate t3)))) 

;goal
(assert (or (<= b0 0) (<= b1 0) (<= b2 0) (<= b3 0) (>= q0 100) (>= q1 100) (>= q2 100) (>= q3 100) (not (constraint b3 q3))))
(check-sat)
(get-value (b3 q3))
(exit)

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
(assert (<= bi 100))
(assert (<= b0 100))
(assert (<= b1 100))
(assert (<= b2 100))
(assert (<= b3 100))
(assert (>= qi 0))
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

(assert (and (= bi 51.0) (= qi 1.0)))
;charging
(assert(= x0 0))
(assert(= b0 (+ bi (* battery_charging_rate t0))))
(assert(= q0 (+ qi (* queue_data_rate t0))))
;program: charge till battery >= 20
(assert (=> (>= bi 20) (= b0 bi)))
(assert (or (=> (< bi 20) (= b0 20)) (= q0 100)))

;flying to D
(assert(= x1 10))
(assert(= x1 (+ x0 (* drone_velocity t1))))
(assert(= b1 (- b0 (* battery_discharge_rate t1))))
(assert(= q1 (+ q0 (* queue_data_rate t1))))

;emptying queue
(assert(= x2 10))
(assert(= q2 (- q1 (* queue_upload_rate t2))))
(assert(= b2 (- b1 (* battery_discharge_rate t2))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1 4) (= b2 4)) (= q2 0)))
(assert (=> (<= b1 4) (= b2 b1)))

;flying back
(assert(= x3 0))
(assert(= x3 (- x2 (* drone_velocity t3))))
(assert(= q3 (+ q2 (* queue_data_rate t3))))
(assert(= b3 (- b2 (* battery_discharge_rate t3))))

;goal
(assert (or (<= b0 0) (<= b1 0) (<= b2 0) (<= b3 0) (>= q0 100) (>= q1 100) (>= q2 100) (>= q3 100) (not (and (= b3 51.0) (= q3 1.0)))))
(check-sat)
(exit)

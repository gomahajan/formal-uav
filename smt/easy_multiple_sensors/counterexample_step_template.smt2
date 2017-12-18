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

(declare-fun s1_qi () Real)
(declare-fun s1_q0 () Real)
(declare-fun s1_q1 () Real)
(declare-fun s1_q2 () Real)
(declare-fun s1_q3 () Real)

(declare-fun s2_qi () Real)
(declare-fun s2_q0 () Real)
(declare-fun s2_q1 () Real)
(declare-fun s2_q2 () Real)
(declare-fun s2_q3 () Real)

(declare-fun t0 () Real)
(declare-fun t1 () Real)
(declare-fun t2 () Real)
(declare-fun t3 () Real)

;parameters
(declare-fun p0 () Real)
(declare-fun p1 () Real)
(declare-fun p2 () Real)
(declare-fun p3 () Real)

;sensor parameters
(declare-fun p4 () Real)
(declare-fun p5 () Real)


;constants
(declare-fun battery_charging_rate () Real)
(declare-fun battery_discharge_rate_fly () Real)
(declare-fun battery_discharge_rate_hover () Real)
(declare-fun queue_data_rate () Real)
(declare-fun queue_upload_rate () Real)
(declare-fun drone_velocity () Real)

(declare-fun s1_loc () Real)
(declare-fun s2_loc () Real)

(assert(= drone_velocity 10))
(assert(= battery_charging_rate 50))
(assert(= battery_discharge_rate_fly 1))
(assert(= battery_discharge_rate_hover 1))
(assert(= queue_data_rate 1))
(assert(= queue_upload_rate 1))

(assert(= s0_loc 10))
(assert(= s1_loc 20))

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
(assert (>= s0_qi 0))
(assert (<= s0_qi 100))
(assert (>= s0_q0 0))
(assert (>= s0_q1 0))
(assert (>= s0_q2 0))
(assert (>= s0_q3 0))
(assert (>= s1_qi 0))
(assert (<= s1_qi 100))
(assert (>= s1_q0 0))
(assert (>= s1_q1 0))
(assert (>= s1_q2 0))
(assert (>= s1_q3 0))
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

(declare-fun choice () Real)

;charging
(assert(= x0 0))
(assert(= b0 (+ bi (* battery_charging_rate t0))))
(assert(= s0_q0 (+ s0_qi (* queue_data_rate t0))))
(assert(= s1_q0 (+ s1_qi (* queue_data_rate t0))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0 and choice of sensor
(assert (and (=> (>= bi p2) (= b0 bi)) (=> (< bi p2) (= b0 p2))))
(assert (or (=> (s0_q0 > p4) (= choice 0)) (=> (s1_q0 > p5)(= choice 1))))

;flying to D
(assert (=> (= choice 0) (= x1 s0_loc)))
(assert (=> (= choice 1) (= x1 s1_loc)))
(assert(= x1 (+ x0 (* drone_velocity t1))))
(assert(= b1 (- b0 (* battery_discharge_rate_fly t1))))
(assert(= s0_q1 (+ s0_q0 (* queue_data_rate t1))))
(assert(= s1_q1 (+ s1_q0 (* queue_data_rate t1))))

;emptying queue
(assert(= x2 x1))
(assert (=> (= choice 0) (and (= s0_q2 (- s0_q1 (* queue_upload_rate t2))) (= s1_q2 (+ s1_q1 (* queue_data_rate t2))))))
(assert (=> (= choice 1) (and (= s1_q2 (- s1_q1 (* queue_upload_rate t2))) (= s0_q2 (+ s0_q1 (* queue_data_rate t2))))))
(assert(= b2 (- b1 (* battery_discharge_rate_hover t2))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1 p3) (= b2 p3)) (= q2 0)))
(assert (=> (<= b1 p3) (= b2 b1)))

;flying back
(assert(= x3 0))
(assert(= x3 (- x2 (* drone_velocity t3))))
(assert(= q3 (+ q2 (* queue_data_rate t3))))
(assert(= b3 (- b2 (* battery_discharge_rate_fly t3))))

;goal
;Question: Does there exist starting battery,queue values such that safety is not maintained
; that is not (invariant => safety)
(assert (and (>= bi p0) (<= qi p1)))
(assert (or (<= b0 0) (<= b1 0) (<= b2 0) (<= b3 0) (>= q0 100) (>= q1 100) (>= q2 100) (>= q3 100) (not (and (>= b3 p0) (<= q3 p1)))))
(check-sat)
(exit)

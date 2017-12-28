(set-logic QF_NRA)

;parameters invariant (numSensors+1)*numSensors
(declare-fun p0 () Real)
(declare-fun p1 () Real)
(declare-fun p2 () Real)
(declare-fun p3 () Real)
(declare-fun p4 () Real)
(declare-fun p5 () Real)

;parameters program numSensors + 2
(declare-fun p6 () Real)
(declare-fun p7 () Real)
(declare-fun p8 () Real)
(declare-fun p9 () Real)

(assert (> p0 1))
(assert (> p3 1))
(assert (> p1 p2))
(assert (> p5 p4))
(assert (> p5 p2))
(assert (> p1 p4))
(assert (= p2 0))
(assert (= p4 0))
;(assert (= p9 2))
;(assert (= p7 20))
;(assert (= p8 20))

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
(assert(= queue_upload_rate 10))
(assert(= s1_loc 10))
(assert(= s2_loc 10))


(assert (<= p0 100))
(assert (>= p0 0))
(assert (<= p1 100))
(assert (>= p1 0))
(assert (<= p2 100))
(assert (>= p2 0))
(assert (<= p3 100))
(assert (>= p3 0))
(assert (<= p4 100))
(assert (>= p4 0))
(assert (<= p5 100))
(assert (>= p5 0))
(assert (<= p6 100))
(assert (>= p6 0))
(assert (<= p7 100))
(assert (>= p7 0))
(assert (<= p8 100))
(assert (>= p8 0))
(assert (<= p9 100))
(assert (>= p9 0))

; Add all phi(counterexample) here
(declare-fun x0_8 () Real)
(declare-fun x1_8 () Real)
(declare-fun x2_8 () Real)
(declare-fun x3_8 () Real)

(declare-fun bi_8 () Real)
(declare-fun b0_8 () Real)
(declare-fun b1_8 () Real)
(declare-fun b2_8 () Real)
(declare-fun b3_8 () Real)

(declare-fun s1_qi_8 () Real)
(declare-fun s1_q0_8 () Real)
(declare-fun s1_q1_8 () Real)
(declare-fun s1_q2_8 () Real)
(declare-fun s1_q3_8 () Real)

(declare-fun s2_qi_8 () Real)
(declare-fun s2_q0_8 () Real)
(declare-fun s2_q1_8 () Real)
(declare-fun s2_q2_8 () Real)
(declare-fun s2_q3_8 () Real)

(declare-fun choice_8 () Real)

(declare-fun t0_8 () Real)
(declare-fun t1_8 () Real)
(declare-fun t2_8 () Real)
(declare-fun t3_8 () Real)

;counterexample
(declare-fun bc_8 () Real)
(declare-fun s1_qc_8 () Real)
(declare-fun s2_qc_8 () Real)

(assert(>= t0_8 0))
(assert(>= t1_8 0))
(assert(>= t2_8 0))
(assert(>= t3_8 0))
(assert (<= bi_8 100))
(assert (<= b0_8 100))
(assert (<= b1_8 100))
(assert (<= b2_8 100))
(assert (<= b3_8 100))
(assert (>= s2_qi_8 0))
(assert (<= s2_qi_8 100))
(assert (>= s2_q0_8 0))
(assert (>= s2_q1_8 0))
(assert (>= s2_q2_8 0))
(assert (>= s2_q3_8 0))
(assert (>= s1_qi_8 0))
(assert (<= s1_qi_8 100))
(assert (>= s1_q0_8 0))
(assert (>= s1_q1_8 0))
(assert (>= s1_q2_8 0))
(assert (>= s1_q3_8 0))

(assert (or (= choice_8 0) (= choice_8 1)))

;charging
(assert(= x0_8 0))
(assert(= b0_8 (+ bi_8 (* battery_charging_rate t0_8))))
(assert(= s1_q0_8 (+ s1_qi_8 (* queue_data_rate t0_8))))
(assert(= s2_q0_8 (+ s2_qi_8 (* queue_data_rate t0_8))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_8 and choice_8 of sensor
(assert (and (=> (>= bi_8 p6) (= b0_8 bi_8)) (=> (< bi_8 p6) (= b0_8 p6))))
(assert (=> (and (>= bi_8 p0) (<= s1_qi_8 p1) (<= (+ s2_qi_8 p2) s1_qi_8)) (= choice_8 0)))
(assert (=> (not (and (>= bi_8 p0) (<= s1_qi_8 p1) (<= (+ s2_qi_8 p2) s1_qi_8))) (= choice_8 1)))


;flying to D
(assert (=> (= choice_8 0) (= x1_8 s1_loc)))
(assert (=> (= choice_8 1) (= x1_8 s2_loc)))
(assert(= x1_8 (+ x0_8 (* drone_velocity t1_8))))
(assert(= b1_8 (- b0_8 (* battery_discharge_rate_fly t1_8))))
(assert(= s1_q1_8 (+ s1_q0_8 (* queue_data_rate t1_8))))
(assert(= s2_q1_8 (+ s2_q0_8 (* queue_data_rate t1_8))))

;emptying queue
(assert(= x2_8 x1_8))
(assert (=> (= choice_8 0) (and (= s1_q2_8 (- s1_q1_8 (* queue_upload_rate t2_8))) (= s2_q2_8 (+ s2_q1_8 (* queue_data_rate t2_8))))))
(assert (=> (= choice_8 1) (and (= s2_q2_8 (- s2_q1_8 (* queue_upload_rate t2_8))) (= s1_q2_8 (+ s1_q1_8 (* queue_data_rate t2_8))))))
(assert(= b2_8 (- b1_8 (* battery_discharge_rate_hover t2_8))))
;program: empty queue till battery <= 4
(assert (=> (= choice_8 0) (and (=> (<= s1_q1_8 p7) (= s1_q2_8 s1_q1_8)) (=> (> s1_q1_8 p7) (= s1_q2_8 p7)))))
(assert (=> (= choice_8 1) (and (=> (<= s2_q1_8 p8) (= s2_q2_8 s2_q1_8)) (=> (> s2_q1_8 p8) (= s2_q2_8 p8)))))

;flying back
(assert(= x3_8 0))
(assert(= x3_8 (- x2_8 (* drone_velocity t3_8))))
(assert(= s1_q3_8 (+ s1_q2_8 (* queue_data_rate t3_8))))
(assert(= s2_q3_8 (+ s2_q2_8 (* queue_data_rate t3_8))))
(assert(= b3_8 (- b2_8 (* battery_discharge_rate_fly t3_8))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_8 78.0) (= s1_qc_8 0.0) (= s2_qc_8 0.0))) here
(assert (and (= bc_8 78.0) (= s1_qc_8 0.0) (= s2_qc_8 0.0)))

(assert (and (= bi_8 bc_8) (= s1_qi_8 s1_qc_8) (= s2_qi_8 s2_qc_8)))
(assert (=> (or (and (>= bi_8 p0) (<= s1_qi_8 p1) (<= (+ s2_qi_8 p2) s1_qi_8)) (and (>= bi_8 p3) (<= (+ s1_qi_8 p4) s2_qi_8) (<= s2_qi_8 p5))) (and (> b0_8 0) (> b1_8 0) (> b2_8 0) (> b3_8 0) (< s1_q0_8 100) (< s1_q1_8 100) (< s1_q2_8 100) (< s1_q3_8 100) (< s2_q0_8 100) (< s2_q1_8 100) (< s2_q2_8 100) (< s2_q3_8 100) (or (and (>= b3_8 p0) (<= s1_q3_8 p1) (<= (+ s2_q3_8 p2) s1_q3_8)) (and (>= b3_8 p3) (<= (+ s1_q3_8 p4) s2_q3_8) (<= s2_q3_8 p5))))))

(declare-fun x0_7 () Real)
(declare-fun x1_7 () Real)
(declare-fun x2_7 () Real)
(declare-fun x3_7 () Real)

(declare-fun bi_7 () Real)
(declare-fun b0_7 () Real)
(declare-fun b1_7 () Real)
(declare-fun b2_7 () Real)
(declare-fun b3_7 () Real)

(declare-fun s1_qi_7 () Real)
(declare-fun s1_q0_7 () Real)
(declare-fun s1_q1_7 () Real)
(declare-fun s1_q2_7 () Real)
(declare-fun s1_q3_7 () Real)

(declare-fun s2_qi_7 () Real)
(declare-fun s2_q0_7 () Real)
(declare-fun s2_q1_7 () Real)
(declare-fun s2_q2_7 () Real)
(declare-fun s2_q3_7 () Real)

(declare-fun choice_7 () Real)

(declare-fun t0_7 () Real)
(declare-fun t1_7
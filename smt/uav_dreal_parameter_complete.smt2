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
(assert (< (+ (* (- p0 9.0) (- p0 9.0)) (+ (* (- p1 9.0) (- p1 9.0)) (+ (* (- p2 10.0) (- p2 10.0)) (+ (* (- p3 1.0) (- p3 1.0)) (+ (* (- p4 9.0) (- p4 9.0)) (+ (* (- p5 9.0) (- p5 9.0)) (+ (* (- p6 10.0) (- p6 10.0)) (+ (* (- p7 1.0) (- p7 1.0)) (+ (* (- p8 9.0) (- p8 9.0)) (* (- p9 9.0) (- p9 9.0))))))))))) 1.0e-2))
(declare-fun x0_1 () Real)
(declare-fun x1_1 () Real)
(declare-fun x2_1 () Real)
(declare-fun x3_1 () Real)

(declare-fun bi_1 () Real)
(declare-fun b0_1 () Real)
(declare-fun b1_1 () Real)
(declare-fun b2_1 () Real)
(declare-fun b3_1 () Real)

(declare-fun s1_qi_1 () Real)
(declare-fun s1_q0_1 () Real)
(declare-fun s1_q1_1 () Real)
(declare-fun s1_q2_1 () Real)
(declare-fun s1_q3_1 () Real)

(declare-fun s2_qi_1 () Real)
(declare-fun s2_q0_1 () Real)
(declare-fun s2_q1_1 () Real)
(declare-fun s2_q2_1 () Real)
(declare-fun s2_q3_1 () Real)

(declare-fun choice_1 () Real)

(declare-fun t0_1 () Real)
(declare-fun t1_1 () Real)
(declare-fun t2_1 () Real)
(declare-fun t3_1 () Real)

;counterexample
(declare-fun bc_1 () Real)
(declare-fun s1_qc_1 () Real)
(declare-fun s2_qc_1 () Real)

(assert(>= t0_1 0))
(assert(>= t1_1 0))
(assert(>= t2_1 0))
(assert(>= t3_1 0))
(assert (<= bi_1 100))
(assert (<= b0_1 100))
(assert (<= b1_1 100))
(assert (<= b2_1 100))
(assert (<= b3_1 100))
(assert (>= s2_qi_1 0))
(assert (<= s2_qi_1 100))
(assert (>= s2_q0_1 0))
(assert (>= s2_q1_1 0))
(assert (>= s2_q2_1 0))
(assert (>= s2_q3_1 0))
(assert (>= s1_qi_1 0))
(assert (<= s1_qi_1 100))
(assert (>= s1_q0_1 0))
(assert (>= s1_q1_1 0))
(assert (>= s1_q2_1 0))
(assert (>= s1_q3_1 0))

(assert (or (= choice_1 0) (= choice_1 1)))

;charging
(assert(= x0_1 0))
(assert(= b0_1 (+ bi_1 (* battery_charging_rate t0_1))))
(assert(= s1_q0_1 (+ s1_qi_1 (* queue_data_rate t0_1))))
(assert(= s2_q0_1 (+ s2_qi_1 (* queue_data_rate t0_1))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_1 and choice_1 of sensor
(assert (and (=> (>= bi_1 p6) (= b0_1 bi_1)) (=> (< bi_1 p6) (= b0_1 p6))))
(assert (=> (and (>= bi_1 p0) (<= s1_qi_1 p1) (<= (+ s2_qi_1 p2) s1_qi_1)) (= choice_1 0)))
(assert (=> (not (and (>= bi_1 p0) (<= s1_qi_1 p1) (<= (+ s2_qi_1 p2) s1_qi_1))) (= choice_1 1)))


;flying to D
(assert (=> (= choice_1 0) (= x1_1 s1_loc)))
(assert (=> (= choice_1 1) (= x1_1 s2_loc)))
(assert(= x1_1 (+ x0_1 (* drone_velocity t1_1))))
(assert(= b1_1 (- b0_1 (* battery_discharge_rate_fly t1_1))))
(assert(= s1_q1_1 (+ s1_q0_1 (* queue_data_rate t1_1))))
(assert(= s2_q1_1 (+ s2_q0_1 (* queue_data_rate t1_1))))

;emptying queue
(assert(= x2_1 x1_1))
(assert (=> (= choice_1 0) (and (= s1_q2_1 (- s1_q1_1 (* queue_upload_rate t2_1))) (= s2_q2_1 (+ s2_q1_1 (* queue_data_rate t2_1))))))
(assert (=> (= choice_1 1) (and (= s2_q2_1 (- s2_q1_1 (* queue_upload_rate t2_1))) (= s1_q2_1 (+ s1_q1_1 (* queue_data_rate t2_1))))))
(assert(= b2_1 (- b1_1 (* battery_discharge_rate_hover t2_1))))
;program: empty queue till battery <= 4
(assert (=> (= choice_1 0) (and (=> (<= s1_q1_1 p7) (= s1_q2_1 s1_q1_1)) (=> (> s1_q1_1 p7) (= s1_q2_1 p7)))))
(assert (=> (= choice_1 1) (and (=> (<= s2_q1_1 p8) (= s2_q2_1 s2_q1_1)) (=> (> s2_q1_1 p8) (= s2_q2_1 p8)))))

;flying back
(assert(= x3_1 0))
(assert(= x3_1 (- x2_1 (* drone_velocity t3_1))))
(assert(= s1_q3_1 (+ s1_q2_1 (* queue_data_rate t3_1))))
(assert(= s2_q3_1 (+ s2_q2_1 (* queue_data_rate t3_1))))
(assert(= b3_1 (- b2_1 (* battery_discharge_rate_fly t3_1))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_1 (/ 10 1)) (= s1_qc_1 (/ 0 1)) (= s2_qc_1 (/ 9 1)))) here
(assert (and (= bc_1 (/ 10 1)) (= s1_qc_1 (/ 0 1)) (= s2_qc_1 (/ 9 1))))

(assert (and (= bi_1 bc_1) (= s1_qi_1 s1_qc_1) (= s2_qi_1 s2_qc_1)))
(assert (=> (or (and (>= bi_1 p0) (<= s1_qi_1 p1) (<= (+ s2_qi_1 p2) s1_qi_1)) (and (>= bi_1 p3) (<= (+ s1_qi_1 p4) s2_qi_1) (<= s2_qi_1 p5))) (and (> b0_1 0) (> b1_1 0) (> b2_1 0) (> b3_1 0) (< s1_q0_1 100) (< s1_q1_1 100) (< s1_q2_1 100) (< s1_q3_1 100) (< s2_q0_1 100) (< s2_q1_1 100) (< s2_q2_1 100) (< s2_q3_1 100) (or (and (>= b3_1 p0) (<= s1_q3_1 p1) (<= (+ s2_q3_1 p2) s1_q3_1)) (and (>= b3_1 p3) (<= (+ s1_q3_1 p4) s2_q3_1) (<= s2_q3_1 p5))))))



(check-sat)
(get-value (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9))
(exit)
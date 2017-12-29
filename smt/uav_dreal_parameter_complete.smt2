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

;(assert (> p0 1))
;(assert (> p3 1))
;(assert (> p1 p2))
;(assert (> p5 p4))
;(assert (> p5 p2))
;(assert (> p1 p4))
;(assert (= p2 0))
;(assert (= p4 0))
;(assert (< p3 90))
;(assert (< p1 90))
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

(define-fun norm ((a Real)) Real
    (ite (< a 0) (* -1 a) a))

(assert(= drone_velocity 10))
(assert(= battery_charging_rate 50))
(assert(= battery_discharge_rate_fly 1))
(assert(= battery_discharge_rate_hover 1))
(assert(= queue_data_rate 1))
(assert(= queue_upload_rate 50))
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
(assert (> (+ (norm (- p0 1.0)) (+ (norm (- p1 1.0)) (+ (norm (- p2 1.0)) (+ (norm (- p3 1.0)) (+ (norm (- p4 1.0)) (+ (norm (- p5 0.5)) (+ (norm (- p6 85.0)) (+ (norm (- p7 1.0)) (+ (norm (- p8 1.0)) (norm (- p9 1.0))))))))))) 1))
(declare-fun x0_3 () Real)
(declare-fun x1_3 () Real)
(declare-fun x2_3 () Real)
(declare-fun x3_3 () Real)

(declare-fun bi_3 () Real)
(declare-fun b0_3 () Real)
(declare-fun b1_3 () Real)
(declare-fun b2_3 () Real)
(declare-fun b3_3 () Real)

(declare-fun s1_qi_3 () Real)
(declare-fun s1_q0_3 () Real)
(declare-fun s1_q1_3 () Real)
(declare-fun s1_q2_3 () Real)
(declare-fun s1_q3_3 () Real)

(declare-fun s2_qi_3 () Real)
(declare-fun s2_q0_3 () Real)
(declare-fun s2_q1_3 () Real)
(declare-fun s2_q2_3 () Real)
(declare-fun s2_q3_3 () Real)

(declare-fun choice_3 () Real)

(declare-fun t0_3 () Real)
(declare-fun t1_3 () Real)
(declare-fun t2_3 () Real)
(declare-fun t3_3 () Real)

;counterexample
(declare-fun bc_3 () Real)
(declare-fun s1_qc_3 () Real)
(declare-fun s2_qc_3 () Real)

(assert(>= t0_3 0))
(assert(>= t1_3 0))
(assert(>= t2_3 0))
(assert(>= t3_3 0))
(assert (<= bi_3 100))
(assert (<= b0_3 100))
(assert (<= b1_3 100))
(assert (<= b2_3 100))
(assert (<= b3_3 100))
(assert (>= s2_qi_3 0))
(assert (<= s2_qi_3 100))
(assert (>= s2_q0_3 0))
(assert (>= s2_q1_3 0))
(assert (>= s2_q2_3 0))
(assert (>= s2_q3_3 0))
(assert (>= s1_qi_3 0))
(assert (<= s1_qi_3 100))
(assert (>= s1_q0_3 0))
(assert (>= s1_q1_3 0))
(assert (>= s1_q2_3 0))
(assert (>= s1_q3_3 0))

(assert (or (= choice_3 0) (= choice_3 1)))

;charging
(assert(= x0_3 0))
(assert(= b0_3 (+ bi_3 (* battery_charging_rate t0_3))))
(assert(= s1_q0_3 (+ s1_qi_3 (* queue_data_rate t0_3))))
(assert(= s2_q0_3 (+ s2_qi_3 (* queue_data_rate t0_3))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_3 and choice_3 of sensor
(assert (and (=> (>= bi_3 p6) (= b0_3 bi_3)) (=> (< bi_3 p6) (= b0_3 p6))))
(assert (=> (and (>= bi_3 p0) (<= s1_qi_3 p1) (<= (+ s2_qi_3 p2) s1_qi_3)) (= choice_3 0)))
(assert (=> (not (and (>= bi_3 p0) (<= s1_qi_3 p1) (<= (+ s2_qi_3 p2) s1_qi_3))) (= choice_3 1)))


;flying to D
(assert (=> (= choice_3 0) (= x1_3 s1_loc)))
(assert (=> (= choice_3 1) (= x1_3 s2_loc)))
(assert(= x1_3 (+ x0_3 (* drone_velocity t1_3))))
(assert(= b1_3 (- b0_3 (* battery_discharge_rate_fly t1_3))))
(assert(= s1_q1_3 (+ s1_q0_3 (* queue_data_rate t1_3))))
(assert(= s2_q1_3 (+ s2_q0_3 (* queue_data_rate t1_3))))

;emptying queue
(assert(= x2_3 x1_3))
(assert (=> (= choice_3 0) (and (= s1_q2_3 (- s1_q1_3 (* queue_upload_rate t2_3))) (= s2_q2_3 (+ s2_q1_3 (* queue_data_rate t2_3))))))
(assert (=> (= choice_3 1) (and (= s2_q2_3 (- s2_q1_3 (* queue_upload_rate t2_3))) (= s1_q2_3 (+ s1_q1_3 (* queue_data_rate t2_3))))))
(assert(= b2_3 (- b1_3 (* battery_discharge_rate_hover t2_3))))
;program: empty queue till battery <= 4
(assert (=> (= choice_3 0) (and (=> (<= s1_q1_3 p7) (= s1_q2_3 s1_q1_3)) (=> (> s1_q1_3 p7) (= s1_q2_3 p7)))))
(assert (=> (= choice_3 1) (and (=> (<= s2_q1_3 p8) (= s2_q2_3 s2_q1_3)) (=> (> s2_q1_3 p8) (= s2_q2_3 p8)))))

;flying back
(assert(= x3_3 0))
(assert(= x3_3 (- x2_3 (* drone_velocity t3_3))))
(assert(= s1_q3_3 (+ s1_q2_3 (* queue_data_rate t3_3))))
(assert(= s2_q3_3 (+ s2_q2_3 (* queue_data_rate t3_3))))
(assert(= b3_3 (- b2_3 (* battery_discharge_rate_fly t3_3))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_3 85.0) (= s1_qc_3 1.0) (= s2_qc_3 0.0))) here
(assert (and (= bc_3 85.0) (= s1_qc_3 1.0) (= s2_qc_3 0.0)))

(assert (and (= bi_3 bc_3) (= s1_qi_3 s1_qc_3) (= s2_qi_3 s2_qc_3)))
(assert (=> (or (and (>= bi_3 p0) (<= s1_qi_3 p1) (<= (+ s2_qi_3 p2) s1_qi_3)) (and (>= bi_3 p3) (<= (+ s1_qi_3 p4) s2_qi_3) (<= s2_qi_3 p5))) (and (> b0_3 0) (> b1_3 0) (> b2_3 0) (> b3_3 0) (< s1_q0_3 100) (< s1_q1_3 100) (< s1_q2_3 100) (< s1_q3_3 100) (< s2_q0_3 100) (< s2_q1_3 100) (< s2_q2_3 100) (< s2_q3_3 100) (or (and (>= b3_3 p0) (<= s1_q3_3 p1) (<= (+ s2_q3_3 p2) s1_q3_3)) (and (>= b3_3 p3) (<= (+ s1_q3_3 p4) s2_q3_3) (<= s2_q3_3 p5))))))

(declare-fun x0_2 () Real)
(declare-fun x1_2 () Real)
(declare-fun x2_2 () Real)
(declare-fun x3_2 () Real)

(declare-fun bi_2 () Real)
(declare-fun b0_2 () Real)
(declare-fun b1_2 () Real)
(declare-fun b2_2 () Real)
(declare-fun b3_2 () Real)

(declare-fun s1_qi_2 () Real)
(declare-fun s1_q0_2 () Real)
(declare-fun s1_q1_2 () Real)
(declare-fun s1_q2_2 () Real)
(declare-fun s1_q3_2 () Real)

(declare-fun s2_qi_2 () Real)
(declare-fun s2_q0_2 () Real)
(declare-fun s2_q1_2 () Real)
(declare-fun s2_q2_2 () Real)
(declare-fun s2_q3_2 () Real)

(declare-fun choice_2 () Real)

(declare-fun t0_2 () Real)
(declare-fun t1_2 () Real)
(declare-fun t2_2 () Real)
(declare-fun t3_2 () Real)

;counterexample
(declare-fun bc_2 () Real)
(declare-fun s1_qc_2 () Real)
(declare-fun s2_qc_2 () Real)

(assert(>= t0_2 0))
(assert(>= t1_2 0))
(assert(>= t2_2 0))
(assert(>= t3_2 0))
(assert (<= bi_2 100))
(assert (<= b0_2 100))
(assert (<= b1_2 100))
(assert (<= b2_2 100))
(assert (<= b3_2 100))
(assert (>= s2_qi_2 0))
(assert (<= s2_qi_2 100))
(assert (>= s2_q0_2 0))
(assert (>= s2_q1_2 0))
(assert (>= s2_q2_2 0))
(assert (>= s2_q3_2 0))
(assert (>= s1_qi_2 0))
(assert (<= s1_qi_2 100))
(assert (>= s1_q0_2 0))
(assert (>= s1_q1_2 0))
(assert (>= s1_q2_2 0))
(assert (>= s1_q3_2 0))

(assert (or (= choice_2 0) (= choice_2 1)))

;charging
(assert(= x0_2 0))
(assert(= b0_2 (+ bi_2 (* battery_charging_rate t0_2))))
(assert(= s1_q0_2 (+ s1_qi_2 (* queue_data_rate t0_2))))
(assert(= s2_q0_2 (+ s2_qi_2 (* queue_data_rate t0_2))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_2 and choice_2 of sensor
(assert (and (=> (>= bi_2 p6) (= b0_2 bi_2)) (=> (< bi_2 p6) (= b0_2 p6))))
(assert (=> (and (>= bi_2 p0) (<= s1_qi_2 p1) (<= (+ s2_qi_2 p2) s1_qi_2)) (= choice_2 0)))
(assert (=> (not (and (>= bi_2 p0) (<= s1_qi_2 p1) (<= (+ s2_qi_2 p2) s1_qi_2))) (= choice_2 1)))


;flying to D
(assert (=> (= choice_2 0) (= x1_2 s1_loc)))
(assert (=> (= choice_2 1) (= x1_2 s2_loc)))
(assert(= x1_2 (+ x0_2 (* drone_velocity t1_2))))
(assert(= b1_2 (- b0_2 (* battery_discharge_rate_fly t1_2))))
(assert(= s1_q1_2 (+ s1_q0_2 (* queue_data_rate t1_2))))
(assert(= s2_q1_2 (+ s2_q0_2 (* queue_data_rate t1_2))))

;emptying queue
(assert(= x2_2 x1_2))
(assert (=> (= choice_2 0) (and (= s1_q2_2 (- s1_q1_2 (* queue_upload_rate t2_2))) (= s2_q2_2 (+ s2_q1_2 (* queue_data_rate t2_2))))))
(assert (=> (= choice_2 1) (and (= s2_q2_2 (- s2_q1_2 (* queue_upload_rate t2_2))) (= s1_q2_2 (+ s1_q1_2 (* queue_data_rate t2_2))))))
(assert(= b2_2 (- b1_2 (* battery_discharge_rate_hover t2_2))))
;program: empty queue till battery <= 4
(assert (=> (= choice_2 0) (and (=> (<= s1_q1_2 p7) (= s1_q2_2 s1_q1_2)) (=> (> s1_q1_2 p7) (= s1_q2_2 p7)))))
(assert (=> (= choice_2 1) (and (=> (<= s2_q1_2 p8) (= s2_q2_2 s2_q1_2)) (=> (> s2_q1_2 p8) (= s2_q2_2 p8)))))

;flying back
(assert(= x3_2 0))
(assert(= x3_2 (- x2_2 (* drone_velocity t3_2))))
(assert(= s1_q3_2 (+ s1_q2_2 (* queue_data_rate t3_2))))
(assert(= s2_q3_2 (+ s2_q2_2 (* queue_data_rate t3_2))))
(assert(= b3_2 (- b2_2 (* battery_discharge_rate_fly t3_2))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_2 60.0) (= s1_qc_2 0.0) (= s2_qc_2 1.0))) here
(assert (and (= bc_2 60.0) (= s1_qc_2 0.0) (= s2_qc_2 1.0)))

(assert (and (= bi_2 bc_2) (= s1_qi_2 s1_qc_2) (= s2_qi_2 s2_qc_2)))
(assert (=> (or (and (>= bi_2 p0) (<= s1_qi_2 p1) (<= (+ s2_qi_2 p2) s1_qi_2)) (and (>= bi_2 p3) (<= (+ s1_qi_2 p4) s2_qi_2) (<= s2_qi_2 p5))) (and (> b0_2 0) (> b1_2 0) (> b2_2 0) (> b3_2 0) (< s1_q0_2 100) (< s1_q1_2 100) (< s1_q2_2 100) (< s1_q3_2 100) (< s2_q0_2 100) (< s2_q1_2 100) (< s2_q2_2 100) (< s2_q3_2 100) (or (and (>= b3_2 p0) (<= s1_q3_2 p1) (<= (+ s2_q3_2 p2) s1_q3_2)) (and (>= b3_2 p3) (<= (+ s1_q3_2 p4) s2_q3_2) (<= s2_q3_2 p5))))))

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
; Add (assert (and (= bc_1 10.0) (= s1_qc_1 0.0) (= s2_qc_1 9.0))) here
(assert (and (= bc_1 10.0) (= s1_qc_1 0.0) (= s2_qc_1 9.0)))

(assert (and (= bi_1 bc_1) (= s1_qi_1 s1_qc_1) (= s2_qi_1 s2_qc_1)))
(assert (=> (or (and (>= bi_1 p0) (<= s1_qi_1 p1) (<= (+ s2_qi_1 p2) s1_qi_1)) (and (>= bi_1 p3) (<= (+ s1_qi_1 p4) s2_qi_1) (<= s2_qi_1 p5))) (and (> b0_1 0) (> b1_1 0) (> b2_1 0) (> b3_1 0) (< s1_q0_1 100) (< s1_q1_1 100) (< s1_q2_1 100) (< s1_q3_1 100) (< s2_q0_1 100) (< s2_q1_1 100) (< s2_q2_1 100) (< s2_q3_1 100) (or (and (>= b3_1 p0) (<= s1_q3_1 p1) (<= (+ s2_q3_1 p2) s1_q3_1)) (and (>= b3_1 p3) (<= (+ s1_q3_1 p4) s2_q3_1) (<= s2_q3_1 p5))))))



(check-sat)
(get-value (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9))
(exit)

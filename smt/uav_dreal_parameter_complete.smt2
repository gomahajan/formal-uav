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
(declare-fun x0_13 () Real)
(declare-fun x1_13 () Real)
(declare-fun x2_13 () Real)
(declare-fun x3_13 () Real)

(declare-fun bi_13 () Real)
(declare-fun b0_13 () Real)
(declare-fun b1_13 () Real)
(declare-fun b2_13 () Real)
(declare-fun b3_13 () Real)

(declare-fun s1_qi_13 () Real)
(declare-fun s1_q0_13 () Real)
(declare-fun s1_q1_13 () Real)
(declare-fun s1_q2_13 () Real)
(declare-fun s1_q3_13 () Real)

(declare-fun s2_qi_13 () Real)
(declare-fun s2_q0_13 () Real)
(declare-fun s2_q1_13 () Real)
(declare-fun s2_q2_13 () Real)
(declare-fun s2_q3_13 () Real)

(declare-fun choice_13 () Real)

(declare-fun t0_13 () Real)
(declare-fun t1_13 () Real)
(declare-fun t2_13 () Real)
(declare-fun t3_13 () Real)

;counterexample
(declare-fun bc_13 () Real)
(declare-fun s1_qc_13 () Real)
(declare-fun s2_qc_13 () Real)

(assert(>= t0_13 0))
(assert(>= t1_13 0))
(assert(>= t2_13 0))
(assert(>= t3_13 0))
(assert (<= bi_13 100))
(assert (<= b0_13 100))
(assert (<= b1_13 100))
(assert (<= b2_13 100))
(assert (<= b3_13 100))
(assert (>= s2_qi_13 0))
(assert (<= s2_qi_13 100))
(assert (>= s2_q0_13 0))
(assert (>= s2_q1_13 0))
(assert (>= s2_q2_13 0))
(assert (>= s2_q3_13 0))
(assert (>= s1_qi_13 0))
(assert (<= s1_qi_13 100))
(assert (>= s1_q0_13 0))
(assert (>= s1_q1_13 0))
(assert (>= s1_q2_13 0))
(assert (>= s1_q3_13 0))

(assert (or (= choice_13 0) (= choice_13 1)))

;charging
(assert(= x0_13 0))
(assert(= b0_13 (+ bi_13 (* battery_charging_rate t0_13))))
(assert(= s1_q0_13 (+ s1_qi_13 (* queue_data_rate t0_13))))
(assert(= s2_q0_13 (+ s2_qi_13 (* queue_data_rate t0_13))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_13 and choice_13 of sensor
(assert (and (=> (>= bi_13 p6) (= b0_13 bi_13)) (=> (< bi_13 p6) (= b0_13 p6))))
(assert (=> (and (>= bi_13 p0) (<= s1_qi_13 p1) (<= (+ s2_qi_13 p2) s1_qi_13)) (= choice_13 0)))
(assert (=> (not (and (>= bi_13 p0) (<= s1_qi_13 p1) (<= (+ s2_qi_13 p2) s1_qi_13))) (= choice_13 1)))


;flying to D
(assert (=> (= choice_13 0) (= x1_13 s1_loc)))
(assert (=> (= choice_13 1) (= x1_13 s2_loc)))
(assert(= x1_13 (+ x0_13 (* drone_velocity t1_13))))
(assert(= b1_13 (- b0_13 (* battery_discharge_rate_fly t1_13))))
(assert(= s1_q1_13 (+ s1_q0_13 (* queue_data_rate t1_13))))
(assert(= s2_q1_13 (+ s2_q0_13 (* queue_data_rate t1_13))))

;emptying queue
(assert(= x2_13 x1_13))
(assert (=> (= choice_13 0) (and (= s1_q2_13 (- s1_q1_13 (* queue_upload_rate t2_13))) (= s2_q2_13 (+ s2_q1_13 (* queue_data_rate t2_13))))))
(assert (=> (= choice_13 1) (and (= s2_q2_13 (- s2_q1_13 (* queue_upload_rate t2_13))) (= s1_q2_13 (+ s1_q1_13 (* queue_data_rate t2_13))))))
(assert(= b2_13 (- b1_13 (* battery_discharge_rate_hover t2_13))))
;program: empty queue till battery <= 4
(assert (=> (= choice_13 0) (and (< (+ s1_q2_13 p9) s2_q2_13))))
(assert (=> (= choice_13 1) (and (< (+ s2_q2_13 p9) s1_q2_13))))

;flying back
(assert(= x3_13 0))
(assert(= x3_13 (- x2_13 (* drone_velocity t3_13))))
(assert(= s1_q3_13 (+ s1_q2_13 (* queue_data_rate t3_13))))
(assert(= s2_q3_13 (+ s2_q2_13 (* queue_data_rate t3_13))))
(assert(= b3_13 (- b2_13 (* battery_discharge_rate_fly t3_13))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_13 1.0) (= s1_qc_13 0.9957818661369309) (= s2_qc_13 2.322461069317157))) here
(assert (and (= bc_13 1.0) (= s1_qc_13 0.9957818661369309) (= s2_qc_13 2.322461069317157)))

(assert (and (= bi_13 bc_13) (= s1_qi_13 s1_qc_13) (= s2_qi_13 s2_qc_13)))
(assert (=> (or (and (>= bi_13 p0) (<= s1_qi_13 p1) (<= (+ s2_qi_13 p2) s1_qi_13)) (and (>= bi_13 p3) (<= (+ s1_qi_13 p4) s2_qi_13) (<= s2_qi_13 p5))) (and (> b0_13 0) (> b1_13 0) (> b2_13 0) (> b3_13 0) (< s1_q0_13 100) (< s1_q1_13 100) (< s1_q2_13 100) (< s1_q3_13 100) (< s2_q0_13 100) (< s2_q1_13 100) (< s2_q2_13 100) (< s2_q3_13 100) (or (and (>= b3_13 p0) (<= s1_q3_13 p1) (<= (+ s2_q3_13 p2) s1_q3_13)) (and (>= b3_13 p3) (<= (+ s1_q3_13 p4) s2_q3_13) (<= s2_q3_13 p5))))))

(declare-fun x0_12 () Real)
(declare-fun x1_12 () Real)
(declare-fun x2_12 () Real)
(declare-fun x3_12 () Real)

(declare-fun bi_12 () Real)
(declare-fun b0_12 () Real)
(declare-fun b1_12 () Real)
(declare-fun b2_12 () Real)
(declare-fun b3_12 () Real)

(declare-fun s1_qi_12 () Real)
(declare-fun s1_q0_12 () Real)
(declare-fun s1_q1_12 () Real)
(declare-fun s1_q2_12 () Real)
(declare-fun s1_q3_12 () Real)

(declare-fun s2_qi_12 () Real)
(declare-fun s2_q0_12 () Real)
(declare-fun s2_q1_12 () Real)
(declare-fun s2_q2_12 () Real)
(declare-fun s2_q3_12 () Real)

(declare-fun choice_12 () Real)

(declare-fun t0_12 () Real)
(declare-fun t1_12 () Real)
(declare-fun t2_12 () Real)
(declare-fun t3_12 () Real)

;counterexample
(declare-fun bc_12 () Real)
(declare-fun s1_qc_12 () Real)
(declare-fun s2_qc_12 () Real)

(assert(>= t0_12 0))
(assert(>= t1_12 0))
(assert(>= t2_12 0))
(assert(>= t3_12 0))
(assert (<= bi_12 100))
(assert (<= b0_12 100))
(assert (<= b1_12 100))
(assert (<= b2_12 100))
(assert (<= b3_12 100))
(assert (>= s2_qi_12 0))
(assert (<= s2_qi_12 100))
(assert (>= s2_q0_12 0))
(assert (>= s2_q1_12 0))
(assert (>= s2_q2_12 0))
(assert (>= s2_q3_12 0))
(assert (>= s1_qi_12 0))
(assert (<= s1_qi_12 100))
(assert (>= s1_q0_12 0))
(assert (>= s1_q1_12 0))
(assert (>= s1_q2_12 0))
(assert (>= s1_q3_12 0))

(assert (or (= choice_12 0) (= choice_12 1)))

;charging
(assert(= x0_12 0))
(assert(= b0_12 (+ bi_12 (* battery_charging_rate t0_12))))
(assert(= s1_q0_12 (+ s1_qi_12 (* queue_data_rate t0_12))))
(assert(= s2_q0_12 (+ s2_qi_12 (* queue_data_rate t0_12))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_12 and choice_12 of sensor
(assert (and (=> (>= bi_12 p6) (= b0_12 bi_12)) (=> (< bi_12 p6) (= b0_12 p6))))
(assert (=> (and (>= bi_12 p0) (<= s1_qi_12 p1) (<= (+ s2_qi_12 p2) s1_qi_12)) (= choice_12 0)))
(assert (=> (not (and (>= bi_12 p0) (<= s1_qi_12 p1) (<= (+ s2_qi_12 p2) s1_qi_12))) (= choice_12 1)))


;flying to D
(assert (=> (= choice_12 0) (= x1_12 s1_loc)))
(assert (=> (= choice_12 1) (= x1_12 s2_loc)))
(assert(= x1_12 (+ x0_12 (* drone_velocity t1_12))))
(assert(= b1_12 (- b0_12 (* battery_discharge_rate_fly t1_12))))
(assert(= s1_q1_12 (+ s1_q0_12 (* queue_data_rate t1_12))))
(assert(= s2_q1_12 (+ s2_q0_12 (* queue_data_rate t1_12))))

;emptying queue
(assert(= x2_12 x1_12))
(assert (=> (= choice_12 0) (and (= s1_q2_12 (- s1_q1_12 (* queue_upload_rate t2_12))) (= s2_q2_12 (+ s2_q1_12 (* queue_data_rate t2_12))))))
(assert (=> (= choice_12 1) (and (= s2_q2_12 (- s2_q1_12 (* queue_upload_rate t2_12))) (= s1_q2_12 (+ s1_q1_12 (* queue_data_rate t2_12))))))
(assert(= b2_12 (- b1_12 (* battery_discharge_rate_hover t2_12))))
;program: empty queue till battery <= 4
(assert (=> (= choice_12 0) (and (< (+ s1_q2_12 p9) s2_q2_12))))
(assert (=> (= choice_12 1) (and (< (+ s2_q2_12 p9) s1_q2_12))))

;flying back
(assert(= x3_12 0))
(assert(= x3_12 (- x2_12 (* drone_velocity t3_12))))
(assert(= s1_q3_12 (+ s1_q2_12 (* queue_data_rate t3_12))))
(assert(= s2_q3_12 (+ s2_q2_12 (* queue_data_rate t3_12))))
(assert(= b3_12 (- b2_12 (* battery_discharge_rate_fly t3_12))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_12 1.0) (= s1_qc_12 0.0) (= s2_qc_12 2.414213317643022))) here
(assert (and (= bc_12 1.0) (= s1_qc_12 0.0) (= s2_qc_12 2.414213317643022)))

(assert (and (= bi_12 bc_12) (= s1_qi_12 s1_qc_12) (= s2_qi_12 s2_qc_12)))
(assert (=> (or (and (>= bi_12 p0) (<= s1_qi_12 p1) (<= (+ s2_qi_12 p2) s1_qi_12)) (and (>= bi_12 p3) (<= (+ s1_qi_12 p4) s2_qi_12) (<= s2_qi_12 p5))) (and (> b0_12 0) (> b1_12 0) (> b2_12 0) (> b3_12 0) (< s1_q0_12 100) (< s1_q1_12 100) (< s1_q2_12 100) (< s1_q3_12 100) (< s2_q0_12 100) (< s2_q1_12 100) (< s2_q2_12 100) (< s2_q3_12 100) (or (and (>= b3_12 p0) (<= s1_q3_12 p1) (<= (+ s2_q3_12 p2) s1_q3_12)) (and (>= b3_12 p3) (<= (+ s1_q3_12 p4) s2_q3_12) (<= s2_q3_12 p5))))))

(declare-fun x0_11 () Real)
(declare-fun x1_11 () Real)
(declare-fun x2_11 () Real)
(declare-fun x3_11 () Real)

(declare-fun bi_11 () Real)
(declare-fun b0_11 () Real)
(declare-fun b1_11 () Real)
(declare-fun b2_11 () Real)
(declare-fun b3_11 () Real)

(declare-fun s1_qi_11 () Real)
(declare-fun s1_q0_11 () Real)
(declare-fun s1_q1_11 () Real)
(declare-fun s1_q2_11 () Real)
(declare-fun s1_q3_11 () Real)

(declare-fun s2_qi_11 () Real)
(declare-fun s2_q0_11 () Real)
(declare-fun s2_q1_11 () Real)
(declare-fun s2_q2_11 () Real)
(declare-fun s2_q3_11 () Real)

(declare-fun choice_11 () Real)

(declare-fun t0_11 () Real)
(declare-fun t1_11 () Real)
(declare-fun t2_11 () Real)
(declare-fun t3_11 () Real)

;counterexample
(declare-fun bc_11 () Real)
(declare-fun s1_qc_11 () Real)
(declare-fun s2_qc_11 () Real)

(assert(>= t0_11 0))
(assert(>= t1_11 0))
(assert(>= t2_11 0))
(assert(>= t3_11 0))
(assert (<= bi_11 100))
(assert (<= b0_11 100))
(assert (<= b1_11 100))
(assert (<= b2_11 100))
(assert (<= b3_11 100))
(assert (>= s2_qi_11 0))
(assert (<= s2_qi_11 100))
(assert (>= s2_q0_11 0))
(assert (>= s2_q1_11 0))
(assert (>= s2_q2_11 0))
(assert (>= s2_q3_11 0))
(assert (>= s1_qi_11 0))
(assert (<= s1_qi_11 100))
(assert (>= s1_q0_11 0))
(assert (>= s1_q1_11 0))
(assert (>= s1_q2_11 0))
(assert (>= s1_q3_11 0))

(assert (or (= choice_11 0) (= choice_11 1)))

;charging
(assert(= x0_11 0))
(assert(= b0_11 (+ bi_11 (* battery_charging_rate t0_11))))
(assert(= s1_q0_11 (+ s1_qi_11 (* queue_data_rate t0_11))))
(assert(= s2_q0_11 (+ s2_qi_11 (* queue_data_rate t0_11))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_11 and choice_11 of sensor
(assert (and (=> (>= bi_11 p6) (= b0_11 bi_11)) (=> (< bi_11 p6) (= b0_11 p6))))
(assert (=> (and (>= bi_11 p0) (<= s1_qi_11 p1) (<= (+ s2_qi_11 p2) s1_qi_11)) (= choice_11 0)))
(assert (=> (not (and (>= bi_11 p0) (<= s1_qi_11 p1) (<= (+ s2_qi_11 p2) s1_qi_11))) (= choice_11 1)))


;flying to D
(assert (=> (= choice_11 0) (= x1_11 s1_loc)))
(assert (=> (= choice_11 1) (= x1_11 s2_loc)))
(assert(= x1_11 (+ x0_11 (* drone_velocity t1_11))))
(assert(= b1_11 (- b0_11 (* battery_discharge_rate_fly t1_11))))
(assert(= s1_q1_11 (+ s1_q0_11 (* queue_data_rate t1_11))))
(assert(= s2_q1_11 (+ s2_q0_11 (* queue_data_rate t1_11))))

;emptying queue
(assert(= x2_11 x1_11))
(assert (=> (= choice_11 0) (and (= s1_q2_11 (- s1_q1_11 (* queue_upload_rate t2_11))) (= s2_q2_11 (+ s2_q1_11 (* queue_data_rate t2_11))))))
(assert (=> (= choice_11 1) (and (= s2_q2_11 (- s2_q1_11 (* queue_upload_rate t2_11))) (= s1_q2_11 (+ s1_q1_11 (* queue_data_rate t2_11))))))
(assert(= b2_11 (- b1_11 (* battery_discharge_rate_hover t2_11))))
;program: empty queue till battery <= 4
(assert (=> (= choice_11 0) (and (< (+ s1_q2_11 p9) s2_q2_11))))
(assert (=> (= choice_11 1) (and (< (+ s2_q2_11 p9) s1_q2_11))))

;flying back
(assert(= x3_11 0))
(assert(= x3_11 (- x2_11 (* drone_velocity t3_11))))
(assert(= s1_q3_11 (+ s1_q2_11 (* queue_data_rate t3_11))))
(assert(= s2_q3_11 (+ s2_q2_11 (* queue_data_rate t3_11))))
(assert(= b3_11 (- b2_11 (* battery_discharge_rate_fly t3_11))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_11 1.0) (= s1_qc_11 3.535472093818765) (= s2_qc_11 3.535472093818765))) here
(assert (and (= bc_11 1.0) (= s1_qc_11 3.535472093818765) (= s2_qc_11 3.535472093818765)))

(assert (and (= bi_11 bc_11) (= s1_qi_11 s1_qc_11) (= s2_qi_11 s2_qc_11)))
(assert (=> (or (and (>= bi_11 p0) (<= s1_qi_11 p1) (<= (+ s2_qi_11 p2) s1_qi_11)) (and (>= bi_11 p3) (<= (+ s1_qi_11 p4) s2_qi_11) (<= s2_qi_11 p5))) (and (> b0_11 0) (> b1_11 0) (> b2_11 0) (> b3_11 0) (< s1_q0_11 100) (< s1_q1_11 100) (< s1_q2_11 100) (< s1_q3_11 100) (< s2_q0_11 100) (< s2_q1_11 100) (< s2_q2_11 100) (< s2_q3_11 100) (or (and (>= b3_11 p0) (<= s1_q3_11 p1) (<= (+ s2_q3_11 p2) s1_q3_11)) (and (>= b3_11 p3) (<= (+ s1_q3_11 p4) s2_q3_11) (<= s2_q3_11 p5))))))

(declare-fun x0_10 () Real)
(declare-fun x1_10 () Real)
(declare-fun x2_10 () Real)
(declare-fun x3_10 () Real)

(declare-fun bi_10 () Real)
(declare-fun b0_10 () Real)
(declare-fun b1_10 () Real)
(declare-fun b2_10 () Real)
(declare-fun b3_10 () Real)

(declare-fun s1_qi_10 () Real)
(declare-fun s1_q0_10 () Real)
(declare-fun s1_q1_10 () Real)
(declare-fun s1_q2_10 () Real)
(declare-fun s1_q3_10 () Real)

(declare-fun s2_qi_10 () Real)
(declare-fun s2_q0_10 () Real)
(declare-fun s2_q1_10 () Real)
(declare-fun s2_q2_10 () Real)
(declare-fun s2_q3_10 () Real)

(declare-fun choice_10 () Real)

(declare-fun t0_10 () Real)
(declare-fun t1_10 () Real)
(declare-fun t2_10 () Real)
(declare-fun t3_10 () Real)

;counterexample
(declare-fun bc_10 () Real)
(declare-fun s1_qc_10 () Real)
(declare-fun s2_qc_10 () Real)

(assert(>= t0_10 0))
(assert(>= t1_10 0))
(assert(>= t2_10 0))
(assert(>= t3_10 0))
(assert (<= bi_10 100))
(assert (<= b0_10 100))
(assert (<= b1_10 100))
(assert (<= b2_10 100))
(assert (<= b3_10 100))
(assert (>= s2_qi_10 0))
(assert (<= s2_qi_10 100))
(assert (>= s2_q0_10 0))
(assert (>= s2_q1_10 0))
(assert (>= s2_q2_10 0))
(assert (>= s2_q3_10 0))
(assert (>= s1_qi_10 0))
(assert (<= s1_qi_10 100))
(assert (>= s1_q0_10 0))
(assert (>= s1_q1_10 0))
(assert (>= s1_q2_10 0))
(assert (>= s1_q3_10 0))

(assert (or (= choice_10 0) (= choice_10 1)))

;charging
(assert(= x0_10 0))
(assert(= b0_10 (+ bi_10 (* battery_charging_rate t0_10))))
(assert(= s1_q0_10 (+ s1_qi_10 (* queue_data_rate t0_10))))
(assert(= s2_q0_10 (+ s2_qi_10 (* queue_data_rate t0_10))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_10 and choice_10 of sensor
(assert (and (=> (>= bi_10 p6) (= b0_10 bi_10)) (=> (< bi_10 p6) (= b0_10 p6))))
(assert (=> (and (>= bi_10 p0) (<= s1_qi_10 p1) (<= (+ s2_qi_10 p2) s1_qi_10)) (= choice_10 0)))
(assert (=> (not (and (>= bi_10 p0) (<= s1_qi_10 p1) (<= (+ s2_qi_10 p2) s1_qi_10))) (= choice_10 1)))


;flying to D
(assert (=> (= choice_10 0) (= x1_10 s1_loc)))
(assert (=> (= choice_10 1) (= x1_10 s2_loc)))
(assert(= x1_10 (+ x0_10 (* drone_velocity t1_10))))
(assert(= b1_10 (- b0_10 (* battery_discharge_rate_fly t1_10))))
(assert(= s1_q1_10 (+ s1_q0_10 (* queue_data_rate t1_10))))
(assert(= s2_q1_10 (+ s2_q0_10 (* queue_data_rate t1_10))))

;emptying queue
(assert(= x2_10 x1_10))
(assert (=> (= choice_10 0) (and (= s1_q2_10 (- s1_q1_10 (* queue_upload_rate t2_10))) (= s2_q2_10 (+ s2_q1_10 (* queue_data_rate t2_10))))))
(assert (=> (= choice_10 1) (and (= s2_q2_10 (- s2_q1_10 (* queue_upload_rate t2_10))) (= s1_q2_10 (+ s1_q1_10 (* queue_data_rate t2_10))))))
(assert(= b2_10 (- b1_10 (* battery_discharge_rate_hover t2_10))))
;program: empty queue till battery <= 4
(assert (=> (= choice_10 0) (and (< (+ s1_q2_10 p9) s2_q2_10))))
(assert (=> (= choice_10 1) (and (< (+ s2_q2_10 p9) s1_q2_10))))

;flying back
(assert(= x3_10 0))
(assert(= x3_10 (- x2_10 (* drone_velocity t3_10))))
(assert(= s1_q3_10 (+ s1_q2_10 (* queue_data_rate t3_10))))
(assert(= s2_q3_10 (+ s2_q2_10 (* queue_data_rate t3_10))))
(assert(= b3_10 (- b2_10 (* battery_discharge_rate_fly t3_10))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_10 1.0) (= s1_qc_10 2.828367168236986) (= s2_qc_10 2.828367168236986))) here
(assert (and (= bc_10 1.0) (= s1_qc_10 2.828367168236986) (= s2_qc_10 2.828367168236986)))

(assert (and (= bi_10 bc_10) (= s1_qi_10 s1_qc_10) (= s2_qi_10 s2_qc_10)))
(assert (=> (or (and (>= bi_10 p0) (<= s1_qi_10 p1) (<= (+ s2_qi_10 p2) s1_qi_10)) (and (>= bi_10 p3) (<= (+ s1_qi_10 p4) s2_qi_10) (<= s2_qi_10 p5))) (and (> b0_10 0) (> b1_10 0) (> b2_10 0) (> b3_10 0) (< s1_q0_10 100) (< s1_q1_10 100) (< s1_q2_10 100) (< s1_q3_10 100) (< s2_q0_10 100) (< s2_q1_10 100) (< s2_q2_10 100) (< s2_q3_10 100) (or (and (>= b3_10 p0) (<= s1_q3_10 p1) (<= (+ s2_q3_10 p2) s1_q3_10)) (and (>= b3_10 p3) (<= (+ s1_q3_10 p4) s2_q3_10) (<= s2_q3_10 p5))))))

(declare-fun x0_9 () Real)
(declare-fun x1_9 () Real)
(declare-fun x2_9 () Real)
(declare-fun x3_9 () Real)

(declare-fun bi_9 () Real)
(declare-fun b0_9 () Real)
(declare-fun b1_9 () Real)
(declare-fun b2_9 () Real)
(declare-fun b3_9 () Real)

(declare-fun s1_qi_9 () Real)
(declare-fun s1_q0_9 () Real)
(declare-fun s1_q1_9 () Real)
(declare-fun s1_q2_9 () Real)
(declare-fun s1_q3_9 () Real)

(declare-fun s2_qi_9 () Real)
(declare-fun s2_q0_9 () Real)
(declare-fun s2_q1_9 () Real)
(declare-fun s2_q2_9 () Real)
(declare-fun s2_q3_9 () Real)

(declare-fun choice_9 () Real)

(declare-fun t0_9 () Real)
(declare-fun t1_9 () Real)
(declare-fun t2_9 () Real)
(declare-fun t3_9 () Real)

;counterexample
(declare-fun bc_9 () Real)
(declare-fun s1_qc_9 () Real)
(declare-fun s2_qc_9 () Real)

(assert(>= t0_9 0))
(assert(>= t1_9 0))
(assert(>= t2_9 0))
(assert(>= t3_9 0))
(assert (<= bi_9 100))
(assert (<= b0_9 100))
(assert (<= b1_9 100))
(assert (<= b2_9 100))
(assert (<= b3_9 100))
(assert (>= s2_qi_9 0))
(assert (<= s2_qi_9 100))
(assert (>= s2_q0_9 0))
(assert (>= s2_q1_9 0))
(assert (>= s2_q2_9 0))
(assert (>= s2_q3_9 0))
(assert (>= s1_qi_9 0))
(assert (<= s1_qi_9 100))
(assert (>= s1_q0_9 0))
(assert (>= s1_q1_9 0))
(assert (>= s1_q2_9 0))
(assert (>= s1_q3_9 0))

(assert (or (= choice_9 0) (= choice_9 1)))

;charging
(assert(= x0_9 0))
(assert(= b0_9 (+ bi_9 (* battery_charging_rate t0_9))))
(assert(= s1_q0_9 (+ s1_qi_9 (* queue_data_rate t0_9))))
(assert(= s2_q0_9 (+ s2_qi_9 (* queue_data_rate t0_9))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_9 and choice_9 of sensor
(assert (and (=> (>= bi_9 p6) (= b0_9 bi_9)) (=> (< bi_9 p6) (= b0_9 p6))))
(assert (=> (and (>= bi_9 p0) (<= s1_qi_9 p1) (<= (+ s2_qi_9 p2) s1_qi_9)) (= choice_9 0)))
(assert (=> (not (and (>= bi_9 p0) (<= s1_qi_9 p1) (<= (+ s2_qi_9 p2) s1_qi_9))) (= choice_9 1)))


;flying to D
(assert (=> (= choice_9 0) (= x1_9 s1_loc)))
(assert (=> (= choice_9 1) (= x1_9 s2_loc)))
(assert(= x1_9 (+ x0_9 (* drone_velocity t1_9))))
(assert(= b1_9 (- b0_9 (* battery_discharge_rate_fly t1_9))))
(assert(= s1_q1_9 (+ s1_q0_9 (* queue_data_rate t1_9))))
(assert(= s2_q1_9 (+ s2_q0_9 (* queue_data_rate t1_9))))

;emptying queue
(assert(= x2_9 x1_9))
(assert (=> (= choice_9 0) (and (= s1_q2_9 (- s1_q1_9 (* queue_upload_rate t2_9))) (= s2_q2_9 (+ s2_q1_9 (* queue_data_rate t2_9))))))
(assert (=> (= choice_9 1) (and (= s2_q2_9 (- s2_q1_9 (* queue_upload_rate t2_9))) (= s1_q2_9 (+ s1_q1_9 (* queue_data_rate t2_9))))))
(assert(= b2_9 (- b1_9 (* battery_discharge_rate_hover t2_9))))
;program: empty queue till battery <= 4
(assert (=> (= choice_9 0) (and (< (+ s1_q2_9 p9) s2_q2_9))))
(assert (=> (= choice_9 1) (and (< (+ s2_q2_9 p9) s1_q2_9))))

;flying back
(assert(= x3_9 0))
(assert(= x3_9 (- x2_9 (* drone_velocity t3_9))))
(assert(= s1_q3_9 (+ s1_q2_9 (* queue_data_rate t3_9))))
(assert(= s2_q3_9 (+ s2_q2_9 (* queue_data_rate t3_9))))
(assert(= b3_9 (- b2_9 (* battery_discharge_rate_fly t3_9))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_9 1.0) (= s1_qc_9 0.0) (= s2_qc_9 1.414213562372983))) here
(assert (and (= bc_9 1.0) (= s1_qc_9 0.0) (= s2_qc_9 1.414213562372983)))

(assert (and (= bi_9 bc_9) (= s1_qi_9 s1_qc_9) (= s2_qi_9 s2_qc_9)))
(assert (=> (or (and (>= bi_9 p0) (<= s1_qi_9 p1) (<= (+ s2_qi_9 p2) s1_qi_9)) (and (>= bi_9 p3) (<= (+ s1_qi_9 p4) s2_qi_9) (<= s2_qi_9 p5))) (and (> b0_9 0) (> b1_9 0) (> b2_9 0) (> b3_9 0) (< s1_q0_9 100) (< s1_q1_9 100) (< s1_q2_9 100) (< s1_q3_9 100) (< s2_q0_9 100) (< s2_q1_9 100) (< s2_q2_9 100) (< s2_q3_9 100) (or (and (>= b3_9 p0) (<= s1_q3_9 p1) (<= (+ s2_q3_9 p2) s1_q3_9)) (and (>= b3_9 p3) (<= (+ s1_q3_9 p4) s2_q3_9) (<= s2_q3_9 p5))))))

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
(assert (=> (= choice_8 0) (and (< (+ s1_q2_8 p9) s2_q2_8))))
(assert (=> (= choice_8 1) (and (< (+ s2_q2_8 p9) s1_q2_8))))

;flying back
(assert(= x3_8 0))
(assert(= x3_8 (- x2_8 (* drone_velocity t3_8))))
(assert(= s1_q3_8 (+ s1_q2_8 (* queue_data_rate t3_8))))
(assert(= s2_q3_8 (+ s2_q2_8 (* queue_data_rate t3_8))))
(assert(= b3_8 (- b2_8 (* battery_discharge_rate_fly t3_8))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_8 1.0) (= s1_qc_8 2.121264199754801) (= s2_qc_8 2.121264199754801))) here
(assert (and (= bc_8 1.0) (= s1_qc_8 2.121264199754801) (= s2_qc_8 2.121264199754801)))

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
(declare-fun t1_7 () Real)
(declare-fun t2_7 () Real)
(declare-fun t3_7 () Real)

;counterexample
(declare-fun bc_7 () Real)
(declare-fun s1_qc_7 () Real)
(declare-fun s2_qc_7 () Real)

(assert(>= t0_7 0))
(assert(>= t1_7 0))
(assert(>= t2_7 0))
(assert(>= t3_7 0))
(assert (<= bi_7 100))
(assert (<= b0_7 100))
(assert (<= b1_7 100))
(assert (<= b2_7 100))
(assert (<= b3_7 100))
(assert (>= s2_qi_7 0))
(assert (<= s2_qi_7 100))
(assert (>= s2_q0_7 0))
(assert (>= s2_q1_7 0))
(assert (>= s2_q2_7 0))
(assert (>= s2_q3_7 0))
(assert (>= s1_qi_7 0))
(assert (<= s1_qi_7 100))
(assert (>= s1_q0_7 0))
(assert (>= s1_q1_7 0))
(assert (>= s1_q2_7 0))
(assert (>= s1_q3_7 0))

(assert (or (= choice_7 0) (= choice_7 1)))

;charging
(assert(= x0_7 0))
(assert(= b0_7 (+ bi_7 (* battery_charging_rate t0_7))))
(assert(= s1_q0_7 (+ s1_qi_7 (* queue_data_rate t0_7))))
(assert(= s2_q0_7 (+ s2_qi_7 (* queue_data_rate t0_7))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_7 and choice_7 of sensor
(assert (and (=> (>= bi_7 p6) (= b0_7 bi_7)) (=> (< bi_7 p6) (= b0_7 p6))))
(assert (=> (and (>= bi_7 p0) (<= s1_qi_7 p1) (<= (+ s2_qi_7 p2) s1_qi_7)) (= choice_7 0)))
(assert (=> (not (and (>= bi_7 p0) (<= s1_qi_7 p1) (<= (+ s2_qi_7 p2) s1_qi_7))) (= choice_7 1)))


;flying to D
(assert (=> (= choice_7 0) (= x1_7 s1_loc)))
(assert (=> (= choice_7 1) (= x1_7 s2_loc)))
(assert(= x1_7 (+ x0_7 (* drone_velocity t1_7))))
(assert(= b1_7 (- b0_7 (* battery_discharge_rate_fly t1_7))))
(assert(= s1_q1_7 (+ s1_q0_7 (* queue_data_rate t1_7))))
(assert(= s2_q1_7 (+ s2_q0_7 (* queue_data_rate t1_7))))

;emptying queue
(assert(= x2_7 x1_7))
(assert (=> (= choice_7 0) (and (= s1_q2_7 (- s1_q1_7 (* queue_upload_rate t2_7))) (= s2_q2_7 (+ s2_q1_7 (* queue_data_rate t2_7))))))
(assert (=> (= choice_7 1) (and (= s2_q2_7 (- s2_q1_7 (* queue_upload_rate t2_7))) (= s1_q2_7 (+ s1_q1_7 (* queue_data_rate t2_7))))))
(assert(= b2_7 (- b1_7 (* battery_discharge_rate_hover t2_7))))
;program: empty queue till battery <= 4
(assert (=> (= choice_7 0) (and (< (+ s1_q2_7 p9) s2_q2_7))))
(assert (=> (= choice_7 1) (and (< (+ s2_q2_7 p9) s1_q2_7))))

;flying back
(assert(= x3_7 0))
(assert(= x3_7 (- x2_7 (* drone_velocity t3_7))))
(assert(= s1_q3_7 (+ s1_q2_7 (* queue_data_rate t3_7))))
(assert(= s2_q3_7 (+ s2_q2_7 (* queue_data_rate t3_7))))
(assert(= b3_7 (- b2_7 (* battery_discharge_rate_fly t3_7))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_7 1.0) (= s1_qc_7 1.414212151933892) (= s2_qc_7 1.414212151933892))) here
(assert (and (= bc_7 1.0) (= s1_qc_7 1.414212151933892) (= s2_qc_7 1.414212151933892)))

(assert (and (= bi_7 bc_7) (= s1_qi_7 s1_qc_7) (= s2_qi_7 s2_qc_7)))
(assert (=> (or (and (>= bi_7 p0) (<= s1_qi_7 p1) (<= (+ s2_qi_7 p2) s1_qi_7)) (and (>= bi_7 p3) (<= (+ s1_qi_7 p4) s2_qi_7) (<= s2_qi_7 p5))) (and (> b0_7 0) (> b1_7 0) (> b2_7 0) (> b3_7 0) (< s1_q0_7 100) (< s1_q1_7 100) (< s1_q2_7 100) (< s1_q3_7 100) (< s2_q0_7 100) (< s2_q1_7 100) (< s2_q2_7 100) (< s2_q3_7 100) (or (and (>= b3_7 p0) (<= s1_q3_7 p1) (<= (+ s2_q3_7 p2) s1_q3_7)) (and (>= b3_7 p3) (<= (+ s1_q3_7 p4) s2_q3_7) (<= s2_q3_7 p5))))))

(declare-fun x0_6 () Real)
(declare-fun x1_6 () Real)
(declare-fun x2_6 () Real)
(declare-fun x3_6 () Real)

(declare-fun bi_6 () Real)
(declare-fun b0_6 () Real)
(declare-fun b1_6 () Real)
(declare-fun b2_6 () Real)
(declare-fun b3_6 () Real)

(declare-fun s1_qi_6 () Real)
(declare-fun s1_q0_6 () Real)
(declare-fun s1_q1_6 () Real)
(declare-fun s1_q2_6 () Real)
(declare-fun s1_q3_6 () Real)

(declare-fun s2_qi_6 () Real)
(declare-fun s2_q0_6 () Real)
(declare-fun s2_q1_6 () Real)
(declare-fun s2_q2_6 () Real)
(declare-fun s2_q3_6 () Real)

(declare-fun choice_6 () Real)

(declare-fun t0_6 () Real)
(declare-fun t1_6 () Real)
(declare-fun t2_6 () Real)
(declare-fun t3_6 () Real)

;counterexample
(declare-fun bc_6 () Real)
(declare-fun s1_qc_6 () Real)
(declare-fun s2_qc_6 () Real)

(assert(>= t0_6 0))
(assert(>= t1_6 0))
(assert(>= t2_6 0))
(assert(>= t3_6 0))
(assert (<= bi_6 100))
(assert (<= b0_6 100))
(assert (<= b1_6 100))
(assert (<= b2_6 100))
(assert (<= b3_6 100))
(assert (>= s2_qi_6 0))
(assert (<= s2_qi_6 100))
(assert (>= s2_q0_6 0))
(assert (>= s2_q1_6 0))
(assert (>= s2_q2_6 0))
(assert (>= s2_q3_6 0))
(assert (>= s1_qi_6 0))
(assert (<= s1_qi_6 100))
(assert (>= s1_q0_6 0))
(assert (>= s1_q1_6 0))
(assert (>= s1_q2_6 0))
(assert (>= s1_q3_6 0))

(assert (or (= choice_6 0) (= choice_6 1)))

;charging
(assert(= x0_6 0))
(assert(= b0_6 (+ bi_6 (* battery_charging_rate t0_6))))
(assert(= s1_q0_6 (+ s1_qi_6 (* queue_data_rate t0_6))))
(assert(= s2_q0_6 (+ s2_qi_6 (* queue_data_rate t0_6))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_6 and choice_6 of sensor
(assert (and (=> (>= bi_6 p6) (= b0_6 bi_6)) (=> (< bi_6 p6) (= b0_6 p6))))
(assert (=> (and (>= bi_6 p0) (<= s1_qi_6 p1) (<= (+ s2_qi_6 p2) s1_qi_6)) (= choice_6 0)))
(assert (=> (not (and (>= bi_6 p0) (<= s1_qi_6 p1) (<= (+ s2_qi_6 p2) s1_qi_6))) (= choice_6 1)))


;flying to D
(assert (=> (= choice_6 0) (= x1_6 s1_loc)))
(assert (=> (= choice_6 1) (= x1_6 s2_loc)))
(assert(= x1_6 (+ x0_6 (* drone_velocity t1_6))))
(assert(= b1_6 (- b0_6 (* battery_discharge_rate_fly t1_6))))
(assert(= s1_q1_6 (+ s1_q0_6 (* queue_data_rate t1_6))))
(assert(= s2_q1_6 (+ s2_q0_6 (* queue_data_rate t1_6))))

;emptying queue
(assert(= x2_6 x1_6))
(assert (=> (= choice_6 0) (and (= s1_q2_6 (- s1_q1_6 (* queue_upload_rate t2_6))) (= s2_q2_6 (+ s2_q1_6 (* queue_data_rate t2_6))))))
(assert (=> (= choice_6 1) (and (= s2_q2_6 (- s2_q1_6 (* queue_upload_rate t2_6))) (= s1_q2_6 (+ s1_q1_6 (* queue_data_rate t2_6))))))
(assert(= b2_6 (- b1_6 (* battery_discharge_rate_hover t2_6))))
;program: empty queue till battery <= 4
(assert (=> (= choice_6 0) (and (< (+ s1_q2_6 p9) s2_q2_6))))
(assert (=> (= choice_6 1) (and (< (+ s2_q2_6 p9) s1_q2_6))))

;flying back
(assert(= x3_6 0))
(assert(= x3_6 (- x2_6 (* drone_velocity t3_6))))
(assert(= s1_q3_6 (+ s1_q2_6 (* queue_data_rate t3_6))))
(assert(= s2_q3_6 (+ s2_q2_6 (* queue_data_rate t3_6))))
(assert(= b3_6 (- b2_6 (* battery_discharge_rate_fly t3_6))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_6 1.0) (= s1_qc_6 0.7071064994013616) (= s2_qc_6 0.7071064994013616))) here
(assert (and (= bc_6 1.0) (= s1_qc_6 0.7071064994013616) (= s2_qc_6 0.7071064994013616)))

(assert (and (= bi_6 bc_6) (= s1_qi_6 s1_qc_6) (= s2_qi_6 s2_qc_6)))
(assert (=> (or (and (>= bi_6 p0) (<= s1_qi_6 p1) (<= (+ s2_qi_6 p2) s1_qi_6)) (and (>= bi_6 p3) (<= (+ s1_qi_6 p4) s2_qi_6) (<= s2_qi_6 p5))) (and (> b0_6 0) (> b1_6 0) (> b2_6 0) (> b3_6 0) (< s1_q0_6 100) (< s1_q1_6 100) (< s1_q2_6 100) (< s1_q3_6 100) (< s2_q0_6 100) (< s2_q1_6 100) (< s2_q2_6 100) (< s2_q3_6 100) (or (and (>= b3_6 p0) (<= s1_q3_6 p1) (<= (+ s2_q3_6 p2) s1_q3_6)) (and (>= b3_6 p3) (<= (+ s1_q3_6 p4) s2_q3_6) (<= s2_q3_6 p5))))))

(declare-fun x0_5 () Real)
(declare-fun x1_5 () Real)
(declare-fun x2_5 () Real)
(declare-fun x3_5 () Real)

(declare-fun bi_5 () Real)
(declare-fun b0_5 () Real)
(declare-fun b1_5 () Real)
(declare-fun b2_5 () Real)
(declare-fun b3_5 () Real)

(declare-fun s1_qi_5 () Real)
(declare-fun s1_q0_5 () Real)
(declare-fun s1_q1_5 () Real)
(declare-fun s1_q2_5 () Real)
(declare-fun s1_q3_5 () Real)

(declare-fun s2_qi_5 () Real)
(declare-fun s2_q0_5 () Real)
(declare-fun s2_q1_5 () Real)
(declare-fun s2_q2_5 () Real)
(declare-fun s2_q3_5 () Real)

(declare-fun choice_5 () Real)

(declare-fun t0_5 () Real)
(declare-fun t1_5 () Real)
(declare-fun t2_5 () Real)
(declare-fun t3_5 () Real)

;counterexample
(declare-fun bc_5 () Real)
(declare-fun s1_qc_5 () Real)
(declare-fun s2_qc_5 () Real)

(assert(>= t0_5 0))
(assert(>= t1_5 0))
(assert(>= t2_5 0))
(assert(>= t3_5 0))
(assert (<= bi_5 100))
(assert (<= b0_5 100))
(assert (<= b1_5 100))
(assert (<= b2_5 100))
(assert (<= b3_5 100))
(assert (>= s2_qi_5 0))
(assert (<= s2_qi_5 100))
(assert (>= s2_q0_5 0))
(assert (>= s2_q1_5 0))
(assert (>= s2_q2_5 0))
(assert (>= s2_q3_5 0))
(assert (>= s1_qi_5 0))
(assert (<= s1_qi_5 100))
(assert (>= s1_q0_5 0))
(assert (>= s1_q1_5 0))
(assert (>= s1_q2_5 0))
(assert (>= s1_q3_5 0))

(assert (or (= choice_5 0) (= choice_5 1)))

;charging
(assert(= x0_5 0))
(assert(= b0_5 (+ bi_5 (* battery_charging_rate t0_5))))
(assert(= s1_q0_5 (+ s1_qi_5 (* queue_data_rate t0_5))))
(assert(= s2_q0_5 (+ s2_qi_5 (* queue_data_rate t0_5))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_5 and choice_5 of sensor
(assert (and (=> (>= bi_5 p6) (= b0_5 bi_5)) (=> (< bi_5 p6) (= b0_5 p6))))
(assert (=> (and (>= bi_5 p0) (<= s1_qi_5 p1) (<= (+ s2_qi_5 p2) s1_qi_5)) (= choice_5 0)))
(assert (=> (not (and (>= bi_5 p0) (<= s1_qi_5 p1) (<= (+ s2_qi_5 p2) s1_qi_5))) (= choice_5 1)))


;flying to D
(assert (=> (= choice_5 0) (= x1_5 s1_loc)))
(assert (=> (= choice_5 1) (= x1_5 s2_loc)))
(assert(= x1_5 (+ x0_5 (* drone_velocity t1_5))))
(assert(= b1_5 (- b0_5 (* battery_discharge_rate_fly t1_5))))
(assert(= s1_q1_5 (+ s1_q0_5 (* queue_data_rate t1_5))))
(assert(= s2_q1_5 (+ s2_q0_5 (* queue_data_rate t1_5))))

;emptying queue
(assert(= x2_5 x1_5))
(assert (=> (= choice_5 0) (and (= s1_q2_5 (- s1_q1_5 (* queue_upload_rate t2_5))) (= s2_q2_5 (+ s2_q1_5 (* queue_data_rate t2_5))))))
(assert (=> (= choice_5 1) (and (= s2_q2_5 (- s2_q1_5 (* queue_upload_rate t2_5))) (= s1_q2_5 (+ s1_q1_5 (* queue_data_rate t2_5))))))
(assert(= b2_5 (- b1_5 (* battery_discharge_rate_hover t2_5))))
;program: empty queue till battery <= 4
(assert (=> (= choice_5 0) (and (< (+ s1_q2_5 p9) s2_q2_5))))
(assert (=> (= choice_5 1) (and (< (+ s2_q2_5 p9) s1_q2_5))))

;flying back
(assert(= x3_5 0))
(assert(= x3_5 (- x2_5 (* drone_velocity t3_5))))
(assert(= s1_q3_5 (+ s1_q2_5 (* queue_data_rate t3_5))))
(assert(= s2_q3_5 (+ s2_q2_5 (* queue_data_rate t3_5))))
(assert(= b3_5 (- b2_5 (* battery_discharge_rate_fly t3_5))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_5 1.0) (= s1_qc_5 0.0) (= s2_qc_5 0.0))) here
(assert (and (= bc_5 1.0) (= s1_qc_5 0.0) (= s2_qc_5 0.0)))

(assert (and (= bi_5 bc_5) (= s1_qi_5 s1_qc_5) (= s2_qi_5 s2_qc_5)))
(assert (=> (or (and (>= bi_5 p0) (<= s1_qi_5 p1) (<= (+ s2_qi_5 p2) s1_qi_5)) (and (>= bi_5 p3) (<= (+ s1_qi_5 p4) s2_qi_5) (<= s2_qi_5 p5))) (and (> b0_5 0) (> b1_5 0) (> b2_5 0) (> b3_5 0) (< s1_q0_5 100) (< s1_q1_5 100) (< s1_q2_5 100) (< s1_q3_5 100) (< s2_q0_5 100) (< s2_q1_5 100) (< s2_q2_5 100) (< s2_q3_5 100) (or (and (>= b3_5 p0) (<= s1_q3_5 p1) (<= (+ s2_q3_5 p2) s1_q3_5)) (and (>= b3_5 p3) (<= (+ s1_q3_5 p4) s2_q3_5) (<= s2_q3_5 p5))))))

(declare-fun x0_4 () Real)
(declare-fun x1_4 () Real)
(declare-fun x2_4 () Real)
(declare-fun x3_4 () Real)

(declare-fun bi_4 () Real)
(declare-fun b0_4 () Real)
(declare-fun b1_4 () Real)
(declare-fun b2_4 () Real)
(declare-fun b3_4 () Real)

(declare-fun s1_qi_4 () Real)
(declare-fun s1_q0_4 () Real)
(declare-fun s1_q1_4 () Real)
(declare-fun s1_q2_4 () Real)
(declare-fun s1_q3_4 () Real)

(declare-fun s2_qi_4 () Real)
(declare-fun s2_q0_4 () Real)
(declare-fun s2_q1_4 () Real)
(declare-fun s2_q2_4 () Real)
(declare-fun s2_q3_4 () Real)

(declare-fun choice_4 () Real)

(declare-fun t0_4 () Real)
(declare-fun t1_4 () Real)
(declare-fun t2_4 () Real)
(declare-fun t3_4 () Real)

;counterexample
(declare-fun bc_4 () Real)
(declare-fun s1_qc_4 () Real)
(declare-fun s2_qc_4 () Real)

(assert(>= t0_4 0))
(assert(>= t1_4 0))
(assert(>= t2_4 0))
(assert(>= t3_4 0))
(assert (<= bi_4 100))
(assert (<= b0_4 100))
(assert (<= b1_4 100))
(assert (<= b2_4 100))
(assert (<= b3_4 100))
(assert (>= s2_qi_4 0))
(assert (<= s2_qi_4 100))
(assert (>= s2_q0_4 0))
(assert (>= s2_q1_4 0))
(assert (>= s2_q2_4 0))
(assert (>= s2_q3_4 0))
(assert (>= s1_qi_4 0))
(assert (<= s1_qi_4 100))
(assert (>= s1_q0_4 0))
(assert (>= s1_q1_4 0))
(assert (>= s1_q2_4 0))
(assert (>= s1_q3_4 0))

(assert (or (= choice_4 0) (= choice_4 1)))

;charging
(assert(= x0_4 0))
(assert(= b0_4 (+ bi_4 (* battery_charging_rate t0_4))))
(assert(= s1_q0_4 (+ s1_qi_4 (* queue_data_rate t0_4))))
(assert(= s2_q0_4 (+ s2_qi_4 (* queue_data_rate t0_4))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0_4 and choice_4 of sensor
(assert (and (=> (>= bi_4 p6) (= b0_4 bi_4)) (=> (< bi_4 p6) (= b0_4 p6))))
(assert (=> (and (>= bi_4 p0) (<= s1_qi_4 p1) (<= (+ s2_qi_4 p2) s1_qi_4)) (= choice_4 0)))
(assert (=> (not (and (>= bi_4 p0) (<= s1_qi_4 p1) (<= (+ s2_qi_4 p2) s1_qi_4))) (= choice_4 1)))


;flying to D
(assert (=> (= choice_4 0) (= x1_4 s1_loc)))
(assert (=> (= choice_4 1) (= x1_4 s2_loc)))
(assert(= x1_4 (+ x0_4 (* drone_velocity t1_4))))
(assert(= b1_4 (- b0_4 (* battery_discharge_rate_fly t1_4))))
(assert(= s1_q1_4 (+ s1_q0_4 (* queue_data_rate t1_4))))
(assert(= s2_q1_4 (+ s2_q0_4 (* queue_data_rate t1_4))))

;emptying queue
(assert(= x2_4 x1_4))
(assert (=> (= choice_4 0) (and (= s1_q2_4 (- s1_q1_4 (* queue_upload_rate t2_4))) (= s2_q2_4 (+ s2_q1_4 (* queue_data_rate t2_4))))))
(assert (=> (= choice_4 1) (and (= s2_q2_4 (- s2_q1_4 (* queue_upload_rate t2_4))) (= s1_q2_4 (+ s1_q1_4 (* queue_data_rate t2_4))))))
(assert(= b2_4 (- b1_4 (* battery_discharge_rate_hover t2_4))))
;program: empty queue till battery <= 4
(assert (=> (= choice_4 0) (and (< (+ s1_q2_4 p9) s2_q2_4))))
(assert (=> (= choice_4 1) (and (< (+ s2_q2_4 p9) s1_q2_4))))

;flying back
(assert(= x3_4 0))
(assert(= x3_4 (- x2_4 (* drone_velocity t3_4))))
(assert(= s1_q3_4 (+ s1_q2_4 (* queue_data_rate t3_4))))
(assert(= s2_q3_4 (+ s2_q2_4 (* queue_data_rate t3_4))))
(assert(= b3_4 (- b2_4 (* battery_discharge_rate_fly t3_4))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_4 30.0) (= s1_qc_4 1.415475542825336) (= s2_qc_4 1.415475542825336))) here
(assert (and (= bc_4 30.0) (= s1_qc_4 1.415475542825336) (= s2_qc_4 1.415475542825336)))

(assert (and (= bi_4 bc_4) (= s1_qi_4 s1_qc_4) (= s2_qi_4 s2_qc_4)))
(assert (=> (or (and (>= bi_4 p0) (<= s1_qi_4 p1) (<= (+ s2_qi_4 p2) s1_qi_4)) (and (>= bi_4 p3) (<= (+ s1_qi_4 p4) s2_qi_4) (<= s2_qi_4 p5))) (and (> b0_4 0) (> b1_4 0) (> b2_4 0) (> b3_4 0) (< s1_q0_4 100) (< s1_q1_4 100) (< s1_q2_4 100) (< s1_q3_4 100) (< s2_q0_4 100) (< s2_q1_4 100) (< s2_q2_4 100) (< s2_q3_4 100) (or (and (>= b3_4 p0) (<= s1_q3_4 p1) (<= (+ s2_q3_4 p2) s1_q3_4)) (and (>= b3_4 p3) (<= (+ s1_q3_4 p4) s2_q3_4) (<= s2_q3_4 p5))))))

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
(assert (=> (= choice_3 0) (and (< (+ s1_q2_3 p9) s2_q2_3))))
(assert (=> (= choice_3 1) (and (< (+ s2_q2_3 p9) s1_q2_3))))

;flying back
(assert(= x3_3 0))
(assert(= x3_3 (- x2_3 (* drone_velocity t3_3))))
(assert(= s1_q3_3 (+ s1_q2_3 (* queue_data_rate t3_3))))
(assert(= s2_q3_3 (+ s2_q2_3 (* queue_data_rate t3_3))))
(assert(= b3_3 (- b2_3 (* battery_discharge_rate_fly t3_3))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_3 30.0) (= s1_qc_3 0.7083702032910295) (= s2_qc_3 0.7083702032910295))) here
(assert (and (= bc_3 30.0) (= s1_qc_3 0.7083702032910295) (= s2_qc_3 0.7083702032910295)))

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
(assert (=> (= choice_2 0) (and (< (+ s1_q2_2 p9) s2_q2_2))))
(assert (=> (= choice_2 1) (and (< (+ s2_q2_2 p9) s1_q2_2))))

;flying back
(assert(= x3_2 0))
(assert(= x3_2 (- x2_2 (* drone_velocity t3_2))))
(assert(= s1_q3_2 (+ s1_q2_2 (* queue_data_rate t3_2))))
(assert(= s2_q3_2 (+ s2_q2_2 (* queue_data_rate t3_2))))
(assert(= b3_2 (- b2_2 (* battery_discharge_rate_fly t3_2))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_2 30.0) (= s1_qc_2 8.877840909090606e-4) (= s2_qc_2 8.877840909090606e-4))) here
(assert (and (= bc_2 30.0) (= s1_qc_2 8.877840909090606e-4) (= s2_qc_2 8.877840909090606e-4)))

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
(assert (=> (= choice_1 0) (and (< (+ s1_q2_1 p9) s2_q2_1))))
(assert (=> (= choice_1 1) (and (< (+ s2_q2_1 p9) s1_q2_1))))

;flying back
(assert(= x3_1 0))
(assert(= x3_1 (- x2_1 (* drone_velocity t3_1))))
(assert(= s1_q3_1 (+ s1_q2_1 (* queue_data_rate t3_1))))
(assert(= s2_q3_1 (+ s2_q2_1 (* queue_data_rate t3_1))))
(assert(= b3_1 (- b2_1 (* battery_discharge_rate_fly t3_1))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_1 30.0) (= s1_qc_1 10.0) (= s2_qc_1 0.0))) here
(assert (and (= bc_1 30.0) (= s1_qc_1 10.0) (= s2_qc_1 0.0)))

(assert (and (= bi_1 bc_1) (= s1_qi_1 s1_qc_1) (= s2_qi_1 s2_qc_1)))
(assert (=> (or (and (>= bi_1 p0) (<= s1_qi_1 p1) (<= (+ s2_qi_1 p2) s1_qi_1)) (and (>= bi_1 p3) (<= (+ s1_qi_1 p4) s2_qi_1) (<= s2_qi_1 p5))) (and (> b0_1 0) (> b1_1 0) (> b2_1 0) (> b3_1 0) (< s1_q0_1 100) (< s1_q1_1 100) (< s1_q2_1 100) (< s1_q3_1 100) (< s2_q0_1 100) (< s2_q1_1 100) (< s2_q2_1 100) (< s2_q3_1 100) (or (and (>= b3_1 p0) (<= s1_q3_1 p1) (<= (+ s2_q3_1 p2) s1_q3_1)) (and (>= b3_1 p3) (<= (+ s1_q3_1 p4) s2_q3_1) (<= s2_q3_1 p5))))))



(check-sat)
(exit)

(set-logic QF_NRA)

;parameters
(declare-fun p0 () Real)
(declare-fun p1 () Real)
(declare-fun p2 () Real)
(declare-fun p3 () Real)

;constants
(declare-fun battery_charging_rate () Real)
(declare-fun battery_discharge_rate_fly () Real)
(declare-fun battery_discharge_rate_hover () Real)
(declare-fun queue_data_rate () Real)
(declare-fun queue_upload_rate () Real)
(declare-fun drone_velocity () Real)

(assert(= drone_velocity 10))
(assert(= battery_charging_rate 50))
(assert(= battery_discharge_rate_fly 1))
(assert(= battery_discharge_rate_hover 1))
(assert(= queue_data_rate 1))
(assert(= queue_upload_rate 1))

(assert (<= p0 100))
(assert (>= p0 0))
(assert (<= p1 100))
(assert (>= p1 0))
(assert (<= p2 100))
(assert (>= p2 0))
(assert (<= p3 100))
(assert (>= p3 0))

; Add all phi(counterexample) here
(declare-fun x0_5 () Real)
(declare-fun x1_5 () Real)
(declare-fun x2_5 () Real)
(declare-fun x3_5 () Real)

(declare-fun bi_5 () Real)
(declare-fun b0_5 () Real)
(declare-fun b1_5 () Real)
(declare-fun b2_5 () Real)
(declare-fun b3_5 () Real)

(declare-fun qi_5 () Real)
(declare-fun q0_5 () Real)
(declare-fun q1_5 () Real)
(declare-fun q2_5 () Real)
(declare-fun q3_5 () Real)

(declare-fun t0_5 () Real)
(declare-fun t1_5 () Real)
(declare-fun t2_5 () Real)
(declare-fun t3_5 () Real)

;counterexample
(declare-fun bc_5 () Real)
(declare-fun qc_5 () Real)

(assert(>= t0_5 0))
(assert(>= t1_5 0))
(assert(>= t2_5 0))
(assert(>= t3_5 0))
(assert (<= bi_5 100))
(assert (<= b0_5 100))
(assert (<= b1_5 100))
(assert (<= b2_5 100))
(assert (<= b3_5 100))
(assert (>= qi_5 0))
(assert (>= q0_5 0))
(assert (>= q1_5 0))
(assert (>= q2_5 0))
(assert (>= q3_5 0))
(assert (<= x0_5 10))
(assert (<= x1_5 10))
(assert (<= x2_5 10))
(assert (<= x3_5 10))
(assert (>= x0_5 0))
(assert (>= x1_5 0))
(assert (>= x2_5 0))
(assert (>= x3_5 0))

;charging
(assert(= x0_5 0))
(assert(= b0_5 (+ bi_5 (* battery_charging_rate t0_5 t0_5))))
(assert(= q0_5 (+ qi_5 (* queue_data_rate t0_5))))
;program: charge till battery >= 20
(assert (=> (>= bi_5 p2) (= b0_5 bi_5)))
(assert (or (=> (< bi_5 p2) (= b0_5 p2)) (= q0_5 100)))

;flying to D
(assert(= x1_5 10))
(assert(= x1_5 (+ x0_5 (* drone_velocity t1_5))))
(assert(= b1_5 (- b0_5 (* battery_discharge_rate_fly t1_5 t1_5))))
(assert(= q1_5 (+ q0_5 (* queue_data_rate t1_5))))

;emptying queue
(assert(= x2_5 10))
(assert(= q2_5 (- q1_5 (* queue_upload_rate t2_5))))
(assert(= b2_5 (- b1_5 (* battery_discharge_rate_hover t2_5))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_5 p3) (= b2_5 p3)) (= q2_5 0)))
(assert (=> (<= b1_5 p3) (= b2_5 b1_5)))

;flying back
(assert(= x3_5 0))
(assert(= x3_5 (- x2_5 (* drone_velocity t3_5))))
(assert(= q3_5 (+ q2_5 (* queue_data_rate t3_5))))
(assert(= b3_5 (- b2_5 (* battery_discharge_rate_fly t3_5))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_5 10.01365074621014) (= qc_5 8.013508838076842))) here
(assert (and (= bc_5 10.01365074621014) (= qc_5 8.013508838076842)))

(assert (and (= bi_5 bc_5) (= qi_5 qc_5)))
(assert (=> (and (>= bi_5 p0) (<= qi_5 p1)) (and (> b0_5 0) (> b1_5 0) (> b2_5 0) (> b3_5 0) (< q0_5 100) (< q1_5 100) (< q2_5 100) (< q3_5 100) (and (>= b3_5 p0) (<= q3_5 p1)))))

(declare-fun x0_4 () Real)
(declare-fun x1_4 () Real)
(declare-fun x2_4 () Real)
(declare-fun x3_4 () Real)

(declare-fun bi_4 () Real)
(declare-fun b0_4 () Real)
(declare-fun b1_4 () Real)
(declare-fun b2_4 () Real)
(declare-fun b3_4 () Real)

(declare-fun qi_4 () Real)
(declare-fun q0_4 () Real)
(declare-fun q1_4 () Real)
(declare-fun q2_4 () Real)
(declare-fun q3_4 () Real)

(declare-fun t0_4 () Real)
(declare-fun t1_4 () Real)
(declare-fun t2_4 () Real)
(declare-fun t3_4 () Real)

;counterexample
(declare-fun bc_4 () Real)
(declare-fun qc_4 () Real)

(assert(>= t0_4 0))
(assert(>= t1_4 0))
(assert(>= t2_4 0))
(assert(>= t3_4 0))
(assert (<= bi_4 100))
(assert (<= b0_4 100))
(assert (<= b1_4 100))
(assert (<= b2_4 100))
(assert (<= b3_4 100))
(assert (>= qi_4 0))
(assert (>= q0_4 0))
(assert (>= q1_4 0))
(assert (>= q2_4 0))
(assert (>= q3_4 0))
(assert (<= x0_4 10))
(assert (<= x1_4 10))
(assert (<= x2_4 10))
(assert (<= x3_4 10))
(assert (>= x0_4 0))
(assert (>= x1_4 0))
(assert (>= x2_4 0))
(assert (>= x3_4 0))

;charging
(assert(= x0_4 0))
(assert(= b0_4 (+ bi_4 (* battery_charging_rate t0_4 t0_4))))
(assert(= q0_4 (+ qi_4 (* queue_data_rate t0_4))))
;program: charge till battery >= 20
(assert (=> (>= bi_4 p2) (= b0_4 bi_4)))
(assert (or (=> (< bi_4 p2) (= b0_4 p2)) (= q0_4 100)))

;flying to D
(assert(= x1_4 10))
(assert(= x1_4 (+ x0_4 (* drone_velocity t1_4))))
(assert(= b1_4 (- b0_4 (* battery_discharge_rate_fly t1_4 t1_4))))
(assert(= q1_4 (+ q0_4 (* queue_data_rate t1_4))))

;emptying queue
(assert(= x2_4 10))
(assert(= q2_4 (- q1_4 (* queue_upload_rate t2_4))))
(assert(= b2_4 (- b1_4 (* battery_discharge_rate_hover t2_4))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_4 p3) (= b2_4 p3)) (= q2_4 0)))
(assert (=> (<= b1_4 p3) (= b2_4 b1_4)))

;flying back
(assert(= x3_4 0))
(assert(= x3_4 (- x2_4 (* drone_velocity t3_4))))
(assert(= q3_4 (+ q2_4 (* queue_data_rate t3_4))))
(assert(= b3_4 (- b2_4 (* battery_discharge_rate_fly t3_4))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_4 10.00739066547913) (= qc_4 8.006362246337238))) here
(assert (and (= bc_4 10.00739066547913) (= qc_4 8.006362246337238)))

(assert (and (= bi_4 bc_4) (= qi_4 qc_4)))
(assert (=> (and (>= bi_4 p0) (<= qi_4 p1)) (and (> b0_4 0) (> b1_4 0) (> b2_4 0) (> b3_4 0) (< q0_4 100) (< q1_4 100) (< q2_4 100) (< q3_4 100) (and (>= b3_4 p0) (<= q3_4 p1)))))

(declare-fun x0_3 () Real)
(declare-fun x1_3 () Real)
(declare-fun x2_3 () Real)
(declare-fun x3_3 () Real)

(declare-fun bi_3 () Real)
(declare-fun b0_3 () Real)
(declare-fun b1_3 () Real)
(declare-fun b2_3 () Real)
(declare-fun b3_3 () Real)

(declare-fun qi_3 () Real)
(declare-fun q0_3 () Real)
(declare-fun q1_3 () Real)
(declare-fun q2_3 () Real)
(declare-fun q3_3 () Real)

(declare-fun t0_3 () Real)
(declare-fun t1_3 () Real)
(declare-fun t2_3 () Real)
(declare-fun t3_3 () Real)

;counterexample
(declare-fun bc_3 () Real)
(declare-fun qc_3 () Real)

(assert(>= t0_3 0))
(assert(>= t1_3 0))
(assert(>= t2_3 0))
(assert(>= t3_3 0))
(assert (<= bi_3 100))
(assert (<= b0_3 100))
(assert (<= b1_3 100))
(assert (<= b2_3 100))
(assert (<= b3_3 100))
(assert (>= qi_3 0))
(assert (>= q0_3 0))
(assert (>= q1_3 0))
(assert (>= q2_3 0))
(assert (>= q3_3 0))
(assert (<= x0_3 10))
(assert (<= x1_3 10))
(assert (<= x2_3 10))
(assert (<= x3_3 10))
(assert (>= x0_3 0))
(assert (>= x1_3 0))
(assert (>= x2_3 0))
(assert (>= x3_3 0))

;charging
(assert(= x0_3 0))
(assert(= b0_3 (+ bi_3 (* battery_charging_rate t0_3 t0_3))))
(assert(= q0_3 (+ qi_3 (* queue_data_rate t0_3))))
;program: charge till battery >= 20
(assert (=> (>= bi_3 p2) (= b0_3 bi_3)))
(assert (or (=> (< bi_3 p2) (= b0_3 p2)) (= q0_3 100)))

;flying to D
(assert(= x1_3 10))
(assert(= x1_3 (+ x0_3 (* drone_velocity t1_3))))
(assert(= b1_3 (- b0_3 (* battery_discharge_rate_fly t1_3 t1_3))))
(assert(= q1_3 (+ q0_3 (* queue_data_rate t1_3))))

;emptying queue
(assert(= x2_3 10))
(assert(= q2_3 (- q1_3 (* queue_upload_rate t2_3))))
(assert(= b2_3 (- b1_3 (* battery_discharge_rate_hover t2_3))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_3 p3) (= b2_3 p3)) (= q2_3 0)))
(assert (=> (<= b1_3 p3) (= b2_3 b1_3)))

;flying back
(assert(= x3_3 0))
(assert(= x3_3 (- x2_3 (* drone_velocity t3_3))))
(assert(= q3_3 (+ q2_3 (* queue_data_rate t3_3))))
(assert(= b3_3 (- b2_3 (* battery_discharge_rate_fly t3_3))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_3 10.00008321645748) (= qc_3 7.999960892417094))) here
(assert (and (= bc_3 10.00008321645748) (= qc_3 7.999960892417094)))

(assert (and (= bi_3 bc_3) (= qi_3 qc_3)))
(assert (=> (and (>= bi_3 p0) (<= qi_3 p1)) (and (> b0_3 0) (> b1_3 0) (> b2_3 0) (> b3_3 0) (< q0_3 100) (< q1_3 100) (< q2_3 100) (< q3_3 100) (and (>= b3_3 p0) (<= q3_3 p1)))))

(declare-fun x0_2 () Real)
(declare-fun x1_2 () Real)
(declare-fun x2_2 () Real)
(declare-fun x3_2 () Real)

(declare-fun bi_2 () Real)
(declare-fun b0_2 () Real)
(declare-fun b1_2 () Real)
(declare-fun b2_2 () Real)
(declare-fun b3_2 () Real)

(declare-fun qi_2 () Real)
(declare-fun q0_2 () Real)
(declare-fun q1_2 () Real)
(declare-fun q2_2 () Real)
(declare-fun q3_2 () Real)

(declare-fun t0_2 () Real)
(declare-fun t1_2 () Real)
(declare-fun t2_2 () Real)
(declare-fun t3_2 () Real)

;counterexample
(declare-fun bc_2 () Real)
(declare-fun qc_2 () Real)

(assert(>= t0_2 0))
(assert(>= t1_2 0))
(assert(>= t2_2 0))
(assert(>= t3_2 0))
(assert (<= bi_2 100))
(assert (<= b0_2 100))
(assert (<= b1_2 100))
(assert (<= b2_2 100))
(assert (<= b3_2 100))
(assert (>= qi_2 0))
(assert (>= q0_2 0))
(assert (>= q1_2 0))
(assert (>= q2_2 0))
(assert (>= q3_2 0))
(assert (<= x0_2 10))
(assert (<= x1_2 10))
(assert (<= x2_2 10))
(assert (<= x3_2 10))
(assert (>= x0_2 0))
(assert (>= x1_2 0))
(assert (>= x2_2 0))
(assert (>= x3_2 0))

;charging
(assert(= x0_2 0))
(assert(= b0_2 (+ bi_2 (* battery_charging_rate t0_2 t0_2))))
(assert(= q0_2 (+ qi_2 (* queue_data_rate t0_2))))
;program: charge till battery >= 20
(assert (=> (>= bi_2 p2) (= b0_2 bi_2)))
(assert (or (=> (< bi_2 p2) (= b0_2 p2)) (= q0_2 100)))

;flying to D
(assert(= x1_2 10))
(assert(= x1_2 (+ x0_2 (* drone_velocity t1_2))))
(assert(= b1_2 (- b0_2 (* battery_discharge_rate_fly t1_2 t1_2))))
(assert(= q1_2 (+ q0_2 (* queue_data_rate t1_2))))

;emptying queue
(assert(= x2_2 10))
(assert(= q2_2 (- q1_2 (* queue_upload_rate t2_2))))
(assert(= b2_2 (- b1_2 (* battery_discharge_rate_hover t2_2))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_2 p3) (= b2_2 p3)) (= q2_2 0)))
(assert (=> (<= b1_2 p3) (= b2_2 b1_2)))

;flying back
(assert(= x3_2 0))
(assert(= x3_2 (- x2_2 (* drone_velocity t3_2))))
(assert(= q3_2 (+ q2_2 (* queue_data_rate t3_2))))
(assert(= b3_2 (- b2_2 (* battery_discharge_rate_fly t3_2))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_2 10.00008321645748) (= qc_2 6.998058193654288))) here
(assert (and (= bc_2 10.00008321645748) (= qc_2 6.998058193654288)))

(assert (and (= bi_2 bc_2) (= qi_2 qc_2)))
(assert (=> (and (>= bi_2 p0) (<= qi_2 p1)) (and (> b0_2 0) (> b1_2 0) (> b2_2 0) (> b3_2 0) (< q0_2 100) (< q1_2 100) (< q2_2 100) (< q3_2 100) (and (>= b3_2 p0) (<= q3_2 p1)))))

(declare-fun x0_1 () Real)
(declare-fun x1_1 () Real)
(declare-fun x2_1 () Real)
(declare-fun x3_1 () Real)

(declare-fun bi_1 () Real)
(declare-fun b0_1 () Real)
(declare-fun b1_1 () Real)
(declare-fun b2_1 () Real)
(declare-fun b3_1 () Real)

(declare-fun qi_1 () Real)
(declare-fun q0_1 () Real)
(declare-fun q1_1 () Real)
(declare-fun q2_1 () Real)
(declare-fun q3_1 () Real)

(declare-fun t0_1 () Real)
(declare-fun t1_1 () Real)
(declare-fun t2_1 () Real)
(declare-fun t3_1 () Real)

;counterexample
(declare-fun bc_1 () Real)
(declare-fun qc_1 () Real)

(assert(>= t0_1 0))
(assert(>= t1_1 0))
(assert(>= t2_1 0))
(assert(>= t3_1 0))
(assert (<= bi_1 100))
(assert (<= b0_1 100))
(assert (<= b1_1 100))
(assert (<= b2_1 100))
(assert (<= b3_1 100))
(assert (>= qi_1 0))
(assert (>= q0_1 0))
(assert (>= q1_1 0))
(assert (>= q2_1 0))
(assert (>= q3_1 0))
(assert (<= x0_1 10))
(assert (<= x1_1 10))
(assert (<= x2_1 10))
(assert (<= x3_1 10))
(assert (>= x0_1 0))
(assert (>= x1_1 0))
(assert (>= x2_1 0))
(assert (>= x3_1 0))

;charging
(assert(= x0_1 0))
(assert(= b0_1 (+ bi_1 (* battery_charging_rate t0_1 t0_1))))
(assert(= q0_1 (+ qi_1 (* queue_data_rate t0_1))))
;program: charge till battery >= 20
(assert (=> (>= bi_1 p2) (= b0_1 bi_1)))
(assert (or (=> (< bi_1 p2) (= b0_1 p2)) (= q0_1 100)))

;flying to D
(assert(= x1_1 10))
(assert(= x1_1 (+ x0_1 (* drone_velocity t1_1))))
(assert(= b1_1 (- b0_1 (* battery_discharge_rate_fly t1_1 t1_1))))
(assert(= q1_1 (+ q0_1 (* queue_data_rate t1_1))))

;emptying queue
(assert(= x2_1 10))
(assert(= q2_1 (- q1_1 (* queue_upload_rate t2_1))))
(assert(= b2_1 (- b1_1 (* battery_discharge_rate_hover t2_1))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1_1 p3) (= b2_1 p3)) (= q2_1 0)))
(assert (=> (<= b1_1 p3) (= b2_1 b1_1)))

;flying back
(assert(= x3_1 0))
(assert(= x3_1 (- x2_1 (* drone_velocity t3_1))))
(assert(= q3_1 (+ q2_1 (* queue_data_rate t3_1))))
(assert(= b3_1 (- b2_1 (* battery_discharge_rate_fly t3_1))))



;goal
;Question: Does there exist parameters such that given battery,queue values, invariant => safety is maintained
; Add (assert (and (= bc_1 10.0) (= qc_1 12.21802139282227))) here
(assert (and (= bc_1 10.0) (= qc_1 12.21802139282227)))

(assert (and (= bi_1 bc_1) (= qi_1 qc_1)))
(assert (=> (and (>= bi_1 p0) (<= qi_1 p1)) (and (> b0_1 0) (> b1_1 0) (> b2_1 0) (> b3_1 0) (< q0_1 100) (< q1_1 100) (< q2_1 100) (< q3_1 100) (and (>= b3_1 p0) (<= q3_1 p1)))))



(check-sat)
(exit)

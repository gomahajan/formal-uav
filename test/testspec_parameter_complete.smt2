(set-logic QF_NRA)
(declare-fun p0 () Real)
(declare-fun p1 () Real)
(declare-fun p2 () Real)
(declare-fun p3 () Real)
(declare-fun p4 () Real)
(declare-fun p5 () Real)
(declare-fun p6 () Real)
(declare-fun p7 () Real)
(declare-fun p8 () Real)
(declare-fun p9 () Real)
(declare-fun battery_charge_rate_fly () Real)
(declare-fun battery_charge_rate_hover () Real)
(declare-fun battery_charging_rate () Real)
(declare-fun drone_velocity () Real)
(declare-fun queue_data_rate () Real)
(declare-fun queue_upload_rate () Real)
(declare-fun s0_loc () Real)
(declare-fun s1_loc () Real)
(define-fun norm ((a Real)) Real
  (ite (< a 0) (* -1 a) a))
(assert (= battery_charge_rate_fly -1.0))
(assert (= battery_charge_rate_hover -1.0))
(assert (= battery_charging_rate 50.0))
(assert (= drone_velocity 10.0))
(assert (= queue_data_rate 1.0))
(assert (= queue_upload_rate 50.0))
(assert (= s0_loc 10.0))
(assert (= s1_loc 10.0))
(assert (>= p0 0.0))
(assert (<= p0 100.0))
(assert (>= p1 0.0))
(assert (<= p1 100.0))
(assert (>= p2 0.0))
(assert (<= p2 100.0))
(assert (>= p3 0.0))
(assert (<= p3 100.0))
(assert (>= p4 0.0))
(assert (<= p4 100.0))
(assert (>= p5 0.0))
(assert (<= p5 100.0))
(assert (>= p6 0.0))
(assert (<= p6 100.0))
(assert (>= p7 0.0))
(assert (<= p7 100.0))
(assert (>= p8 0.0))
(assert (<= p8 100.0))
(assert (>= p9 0.0))
(assert (<= p9 100.0))

(assert (> (+ (norm (- p0 9.0)) (+ (norm (- p1 0.0)) (+ (norm (- p2 10.0)) (+ (norm (- p3 1.0)) (+ (norm (- p4 9.0)) (+ (norm (- p5 9.0)) (+ (norm (- p6 10.0)) (+ (norm (- p7 1.0)) (+ (norm (- p8 9.0)) (norm (- p9 9.0))))))))))) 1))
(declare-fun x0_1 () Real)
(declare-fun x1_1 () Real)
(declare-fun x2_1 () Real)
(declare-fun x3_1 () Real)
(declare-fun bi_1 () Real)
(declare-fun b0_1 () Real)
(declare-fun b1_1 () Real)
(declare-fun b2_1 () Real)
(declare-fun b3_1 () Real)
(declare-fun s0_qi_1 () Real)
(declare-fun s0_q0_1 () Real)
(declare-fun s0_q1_1 () Real)
(declare-fun s0_q2_1 () Real)
(declare-fun s0_q3_1 () Real)
(declare-fun s1_qi_1 () Real)
(declare-fun s1_q0_1 () Real)
(declare-fun s1_q1_1 () Real)
(declare-fun s1_q2_1 () Real)
(declare-fun s1_q3_1 () Real)
(declare-fun t0_1 () Real)
(declare-fun t1_1 () Real)
(declare-fun t2_1 () Real)
(declare-fun t3_1 () Real)
(declare-fun bc_1 () Real)
(declare-fun s0_qc_1 () Real)
(declare-fun s1_qc_1 () Real)
(assert (>= t0_1 0.0))
(assert (>= t1_1 0.0))
(assert (>= t2_1 0.0))
(assert (>= t3_1 0.0))
(assert (<= bi_1 100.0))
(assert (<= b0_1 100.0))
(assert (<= b1_1 100.0))
(assert (<= b2_1 100.0))
(assert (<= b3_1 100.0))
(assert (>= s0_qi_1 0.0))
(assert (>= s0_q0_1 0.0))
(assert (>= s0_q1_1 0.0))
(assert (>= s0_q2_1 0.0))
(assert (>= s0_q3_1 0.0))
(assert (>= s1_qi_1 0.0))
(assert (>= s1_q0_1 0.0))
(assert (>= s1_q1_1 0.0))
(assert (>= s1_q2_1 0.0))
(assert (>= s1_q3_1 0.0))
(assert (<= s0_qi_1 100.0))
(assert (<= s1_qi_1 100.0))
(declare-fun choice_1 () Real)
(assert (or (= choice_1 0.0) (= choice_1 1.0)))


;charging
(assert (= x0_1 0))
(assert (= b0_1 (+ bi_1 (* battery_charging_rate t0_1))))
(assert (= s0_q0_1 (+ s0_qi_1 (* queue_data_rate t0_1))))
(assert (= s1_q0_1 (+ s1_qi_1 (* queue_data_rate t0_1))))
(assert (and (=> (>= bi_1 p6) (= b0_1 bi_1)) (=> (< bi_1 p6) (= b0_1 p6))))
(assert (=> (and (and (>= bi_1 p0) (<= s0_qi_1 p1)) (<= (+ s1_qi_1 p2) s0_qi_1)) (= choice_1 0.0)))
(assert (=> (not (and (and (>= bi_1 p0) (<= s0_qi_1 p1)) (<= (+ s1_qi_1 p2) s0_qi_1))) (= choice_1 1.0)))


;flying to sensors
(assert (=> (= choice_1 0.0) (= x1_1 s0_loc)))
(assert (=> (= choice_1 1.0) (= x1_1 s1_loc)))
(assert (= x1_1 (+ x0_1 (* drone_velocity t1_1))))
(assert (= b1_1 (+ b0_1 (* battery_charge_rate_fly t1_1))))
(assert (= s0_q1_1 (+ s0_q0_1 (* queue_data_rate t1_1))))
(assert (= s1_q1_1 (+ s1_q0_1 (* queue_data_rate t1_1))))


;Collecting data
(assert (= x2_1 x1_1))
(assert (= b2_1 (+ b1_1 (* battery_charge_rate_hover t2_1))))
(assert (=> (= choice_1 0.0) (and (= s0_q2_1 (- s0_q1_1 (* queue_upload_rate t2_1))) (= s1_q2_1 (+ s1_q1_1 (* queue_data_rate t2_1))))))
(assert (=> (= choice_1 1.0) (and (= s1_q2_1 (- s1_q1_1 (* queue_upload_rate t2_1))) (= s0_q2_1 (+ s0_q1_1 (* queue_data_rate t2_1))))))
(assert (and (=> (= choice_1 0.0) (=> (<= s0_q1_1 p7) (= s0_q2_1 s0_q1_1))) (=> (> s0_q1_1 p7) (= s0_q2_1 p7))))
(assert (and (=> (= choice_1 1.0) (=> (<= s1_q1_1 p8) (= s1_q2_1 s1_q1_1))) (=> (> s1_q1_1 p8) (= s1_q2_1 p8))))


;flying back
(assert (= x3_1 0))
(assert (= x3_1 (+ x2_1 (- (* drone_velocity t3_1)))))
(assert (= b3_1 (+ b2_1 (* battery_charge_rate_fly t3_1))))
(assert (= s0_q3_1 (+ s0_q2_1 (* queue_data_rate t3_1))))
(assert (= s1_q3_1 (+ s1_q2_1 (* queue_data_rate t3_1))))

(assert (and (= bc_1 10.0) (= s0_qc_1 0.0) (= s1_qc_1 9.0)))

(assert (and (= bi_1 bc_1) (= s0_qi_1 s0_qc_1) (= s1_qi_1 s1_qc_1)))


;Goal
(assert (not (=>(or (and (and (>= bi_1 p0) (<= s0_qi_1 p1)) (<= (+ s1_qi_1 p2) s0_qi_1)) (and (and (>= bi_1 p3) (<= s1_qi_1 p5)) (<= (+ s0_qi_1 p4) s1_qi_1)))(and (and (> b0_1 0.0) (> b1_1 0.0) (> b2_1 0.0) (> b3_1 0.0) (< s0_q0_1 100.0) (< s0_q1_1 100.0) (< s0_q2_1 100.0) (< s0_q3_1 100.0) (< s1_q0_1 100.0) (< s1_q1_1 100.0) (< s1_q2_1 100.0) (< s1_q3_1 100.0))(or (and (and (>= b3_1 p0) (<= s0_q3_1 p1)) (<= (+ s1_q3_1 p2) s0_q3_1)) (and (and (>= b3_1 p3) (<= s1_q3_1 p5)) (<= (+ s0_q3_1 p4) s1_q3_1)))))))



(check-sat)
(get-value (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9))
(exit)

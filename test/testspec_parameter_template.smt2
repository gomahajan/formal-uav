(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun bi () Real)
(declare-fun b0 () Real)
(declare-fun b1 () Real)
(declare-fun b2 () Real)
(declare-fun b3 () Real)
(declare-fun s0_qi () Real)
(declare-fun s0_q0 () Real)
(declare-fun s0_q1 () Real)
(declare-fun s0_q2 () Real)
(declare-fun s0_q3 () Real)
(declare-fun s1_qi () Real)
(declare-fun s1_q0 () Real)
(declare-fun s1_q1 () Real)
(declare-fun s1_q2 () Real)
(declare-fun s1_q3 () Real)
(declare-fun t0 () Real)
(declare-fun t1 () Real)
(declare-fun t2 () Real)
(declare-fun t3 () Real)
(declare-fun bc () Real)
(declare-fun s0_qc () Real)
(declare-fun s1_qc () Real)
(assert (>= t0 0.0))
(assert (>= t1 0.0))
(assert (>= t2 0.0))
(assert (>= t3 0.0))
(assert (<= bi 100.0))
(assert (<= b0 100.0))
(assert (<= b1 100.0))
(assert (<= b2 100.0))
(assert (<= b3 100.0))
(assert (>= s0_qi 0.0))
(assert (>= s0_q0 0.0))
(assert (>= s0_q1 0.0))
(assert (>= s0_q2 0.0))
(assert (>= s0_q3 0.0))
(assert (>= s1_qi 0.0))
(assert (>= s1_q0 0.0))
(assert (>= s1_q1 0.0))
(assert (>= s1_q2 0.0))
(assert (>= s1_q3 0.0))
(assert (<= s0_qi 100.0))
(assert (<= s1_qi 100.0))
(declare-fun choice () Real)
(assert (or (= choice 0.0) (= choice 1.0)))


;charging
(assert (= x0 0))
(assert (= b0 (+ bi (* battery_charging_rate t0))))
(assert (= s0_q0 (+ s0_qi (* queue_data_rate t0))))
(assert (= s1_q0 (+ s1_qi (* queue_data_rate t0))))
(assert (and (=> (>= bi p6) (= b0 bi)) (=> (< bi p6) (= b0 p6))))
(assert (=> (and (and (>= bi p0) (<= s0_qi p1)) (<= (+ s1_qi p2) s0_qi)) (= choice 0.0)))
(assert (=> (not (and (and (>= bi p0) (<= s0_qi p1)) (<= (+ s1_qi p2) s0_qi))) (= choice 1.0)))


;flying to sensors
(assert (=> (= choice 0.0) (= x1 s0_loc)))
(assert (=> (= choice 1.0) (= x1 s1_loc)))
(assert (= x1 (+ x0 (* drone_velocity t1))))
(assert (= b1 (+ b0 (* battery_charge_rate_fly t1))))
(assert (= s0_q1 (+ s0_q0 (* queue_data_rate t1))))
(assert (= s1_q1 (+ s1_q0 (* queue_data_rate t1))))


;Collecting data
(assert (= x2 x1))
(assert (= b2 (+ b1 (* battery_charge_rate_hover t2))))
(assert (=> (= choice 0.0) (and (= s0_q2 (- s0_q1 (* queue_upload_rate t2))) (= s1_q2 (+ s1_q1 (* queue_data_rate t2))))))
(assert (=> (= choice 1.0) (and (= s1_q2 (- s1_q1 (* queue_upload_rate t2))) (= s0_q2 (+ s0_q1 (* queue_data_rate t2))))))
(assert (and (=> (= choice 0.0) (=> (<= s0_q1 p7) (= s0_q2 s0_q1))) (=> (> s0_q1 p7) (= s0_q2 p7))))
(assert (and (=> (= choice 1.0) (=> (<= s1_q1 p8) (= s1_q2 s1_q1))) (=> (> s1_q1 p8) (= s1_q2 p8))))


;flying back
(assert (= x3 0))
(assert (= x3 (+ x2 (- (* drone_velocity t3)))))
(assert (= b3 (+ b2 (* battery_charge_rate_fly t3))))
(assert (= s0_q3 (+ s0_q2 (* queue_data_rate t3))))
(assert (= s1_q3 (+ s1_q2 (* queue_data_rate t3))))

batteryvalue

(assert (and (= bi bc) (= s0_qi s0_qc) (= s1_qi s1_qc)))


;Goal
(assert (=>(or (and (and (>= bi p0) (<= s0_qi p1)) (<= (+ s1_qi p2) s0_qi)) (and (and (>= bi p3) (<= s1_qi p5)) (<= (+ s0_qi p4) s1_qi)))(and (and (> b0 0.0) (> b1 0.0) (> b2 0.0) (> b3 0.0) (< s0_q0 100.0) (< s0_q1 100.0) (< s0_q2 100.0) (< s0_q3 100.0) (< s1_q0 100.0) (< s1_q1 100.0) (< s1_q2 100.0) (< s1_q3 100.0))(or (and (and (>= b3 p0) (<= s0_q3 p1)) (<= (+ s1_q3 p2) s0_q3)) (and (and (>= b3 p3) (<= s1_q3 p5)) (<= (+ s0_q3 p4) s1_q3))))))

(set-logic QF_NRA)
(declare-fun xi () Real)
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
(declare-fun battery_charging_rate () Real)
(declare-fun battery_discharge_rate_fly () Real)
(declare-fun battery_discharge_rate_hover () Real)
(declare-fun drone_velocity () Real)
(declare-fun queue_data_rate () Real)
(declare-fun queue_upload_rate () Real)
(declare-fun s0_loc () Real)
(declare-fun s1_loc () Real)
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
(assert (= battery_charging_rate 50.0))
(assert (= battery_discharge_rate_fly 1.0))
(assert (= battery_discharge_rate_hover 1.0))
(assert (= drone_velocity 10.0))
(assert (= queue_data_rate 1.0))
(assert (= queue_upload_rate 1.0))
(assert (= s0_loc 10.0))
(assert (= s1_loc 15.0))
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

parametervalues

(declare-fun choice () Real)
(assert (or (= choice 0.0) (= choice 1.0)))


;charging
(assert (= xi 0))
(assert (= x0 (+ xi 0.0)))
(assert (= b0 (+ bi (* battery_charging_rate t0))))
(assert (= s0_q0 (+ s0_qi (* queue_data_rate t0))))
(assert (= s1_q0 (+ s1_qi (* queue_data_rate t0))))
(assert (and (=> (>= bi p6) (= b0 bi)) (=> (< bi p6) (= b0 p6))))
(assert (=> (and (and (>= bi p0) (<= s0_qi p1)) (<= (+ s1_qi p2) s0_q1)) (= choice 0.0)))
(assert (=> (not (and (and (>= bi p0) (<= s0_qi p1)) (<= (+ s1_qi p2) s0_q1))) (= choice 1.0)))


;flying to sensors
(assert (=> (= choice 0.0) (= x1 s0_loc)))
(assert (=> (= choice 1.0) (= x1 s1_loc)))
(assert (= x1 (+ x0 (* drone_velocity t1))))
(assert (= b1 (+ b0 (* battery_discharge_rate_fly t1))))
(assert (= s0_q1 (+ s0_q0 (* queue_data_rate t1))))
(assert (= s1_q1 (+ s1_q0 (* queue_data_rate t1))))


;Collecting data
(assert (= x2 x1))
(assert (= b2 (+ b1 (* battery_discharge_rate_hover t2))))
(assert (=> (= choice 0.0) (and (= s0_q2 (- s0_q1 (* queue_upload_rate t2))) (= s1_q1 (+ s1_q2 (* queue_data_rate t2))))))
(assert (=> (= choice 1.0) (and (= s1_q2 (- s1_q1 (* queue_upload_rate t2))) (= s0_q1 (+ s0_q2 (* queue_data_rate t2))))))
(assert (and (=> (= choice 0.0) (=> (<= s0_q1 p7) (= s0_q2 s0_q1))) (=> (> s0_q1 p7) (= s0_q2 p7))))
(assert (and (=> (= choice 1.0) (=> (<= s1_q1 p8) (= s1_q2 s1_q1))) (=> (> s1_q1 p8) (= s1_q2 p8))))


;flying back
(assert (= x3 0))
(assert (= x3 (+ x2 (- (* drone_velocity t3)))))
(assert (= b3 (+ b2 (* battery_discharge_rate_fly t3))))
(assert (= s0_q3 (+ s0_q2 (* queue_data_rate t3))))
(assert (= s1_q3 (+ s1_q2 (* queue_data_rate t3))))


;Goal
(assert (not (=>(and (and (and (>= bi p0) (<= s0_qi p1)) (<= (+ s1_qi p2) s0_qi)) (and (and (>= bi p3) (<= s0_qi p5)) (<= (+ s0_qi p4) s1_qi)))(and (and (> b0 0.0) (> b1 0.0) (> b2 0.0) (> b3 0.0) (< s0_q0 100.0) (< s0_q1 100.0) (< s0_q2 100.0) (< s0_q3 100.0) (< s1_q0 100.0) (< s1_q1 100.0) (< s1_q2 100.0) (< s1_q3 100.0))(and (and (and (>= b3 p0) (<= s0_q3 p1)) (<= (+ s1_q3 p2) s0_q3)) (and (and (>= b3 p3) (<= s0_q3 p5)) (<= (+ s0_q3 p4) s1_q3)))))))
(check-sat)
(exit)

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

;constants
(declare-fun battery_charging_rate () Real)
(declare-fun battery_discharge_rate_fly () Real)
(declare-fun battery_discharge_rate_hover () Real)
(declare-fun queue_data_rate () Real)
(declare-fun queue_upload_rate () Real)
(declare-fun drone_velocity () Real)

(declare-fun s1_loc () Real)
(declare-fun s2_loc () Real)
(declare-fun choice () Real)

(assert(= drone_velocity 10))
(assert(= battery_charging_rate 50))
(assert(= battery_discharge_rate_fly 1))
(assert(= battery_discharge_rate_hover 1))
(assert(= queue_data_rate 1))
(assert(= queue_upload_rate 10))

(assert(= s1_loc 10))
(assert(= s2_loc 10))

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
(assert (>= s2_qi 0))
(assert (<= s2_qi 100))
(assert (>= s2_q0 0))
(assert (>= s2_q1 0))
(assert (>= s2_q2 0))
(assert (>= s2_q3 0))
(assert (>= s1_qi 0))
(assert (<= s1_qi 100))
(assert (>= s1_q0 0))
(assert (>= s1_q1 0))
(assert (>= s1_q2 0))
(assert (>= s1_q3 0))

;template
(assert (= p0 30.0))
(assert (= p1 12.0))
(assert (= p2 0.0))
(assert (= p3 1.0))
(assert (= p4 0.0))
(assert (= p5 5.535472093818765))
(assert (= p6 1.0))
(assert (= p7 0.0))
(assert (= p8 0.0))
(assert (= p9 0.0))

(assert (and (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 1.0) 2.0) (^ (- s1_qi 0.0) 2.0)) (^ (- s2_qi 2.414213317643022) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 1.0) 2.0) (^ (- s1_qi 3.535472093818765) 2.0)) (^ (- s2_qi 3.535472093818765) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 1.0) 2.0) (^ (- s1_qi 2.828367168236986) 2.0)) (^ (- s2_qi 2.828367168236986) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 1.0) 2.0) (^ (- s1_qi 0.0) 2.0)) (^ (- s2_qi 1.414213562372983) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 1.0) 2.0) (^ (- s1_qi 2.121264199754801) 2.0)) (^ (- s2_qi 2.121264199754801) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 1.0) 2.0) (^ (- s1_qi 1.414212151933892) 2.0)) (^ (- s2_qi 1.414212151933892) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 1.0) 2.0) (^ (- s1_qi 0.7071064994013616) 2.0)) (^ (- s2_qi 0.7071064994013616) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 1.0) 2.0) (^ (- s1_qi 0.0) 2.0)) (^ (- s2_qi 0.0) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 30.0) 2.0) (^ (- s1_qi 1.415475542825336) 2.0)) (^ (- s2_qi 1.415475542825336) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 30.0) 2.0) (^ (- s1_qi 0.7083702032910295) 2.0)) (^ (- s2_qi 0.7083702032910295) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 30.0) 2.0) (^ (- s1_qi 8.877840909090606e-4) 2.0)) (^ (- s2_qi 8.877840909090606e-4) 2.0)))) (not (>= (^ 1.0 2.0) (+ (+ (^ (- bi 30.0) 2.0) (^ (- s1_qi 10.0) 2.0)) (^ (- s2_qi 0.0) 2.0))))))
;sample (assert (= p0 1))
;sample (assert (= p1 1))
;sample (assert (= p2 1))
;sample (assert (= p3 1))

(assert (or (= choice 0) (= choice 1)))

;charging
(assert(= x0 0))
(assert(= b0 (+ bi (* battery_charging_rate t0))))
(assert(= s1_q0 (+ s1_qi (* queue_data_rate t0))))
(assert(= s2_q0 (+ s2_qi (* queue_data_rate t0))))
; TODO: allow to stay when battery = 100
;program: charge till battery >= 20
;decide when to leave, that is b0 and choice of sensor
(assert (and (=> (>= bi p6) (= b0 bi)) (=> (< bi p6) (= b0 p6))))
(assert (=> (and (>= bi p0) (<= s1_qi p1) (<= (+ s2_qi p2) s1_qi)) (= choice 0)))
(assert (=> (not (and (>= bi p0) (<= s1_qi p1) (<= (+ s2_qi p2) s1_qi))) (= choice 1)))


;flying to D
(assert (=> (= choice 0) (= x1 s1_loc)))
(assert (=> (= choice 1) (= x1 s2_loc)))
(assert(= x1 (+ x0 (* drone_velocity t1))))
(assert(= b1 (- b0 (* battery_discharge_rate_fly t1))))
(assert(= s1_q1 (+ s1_q0 (* queue_data_rate t1))))
(assert(= s2_q1 (+ s2_q0 (* queue_data_rate t1))))

;emptying queue
(assert(= x2 x1))
(assert (=> (= choice 0) (and (= s1_q2 (- s1_q1 (* queue_upload_rate t2))) (= s2_q2 (+ s2_q1 (* queue_data_rate t2))))))
(assert (=> (= choice 1) (and (= s2_q2 (- s2_q1 (* queue_upload_rate t2))) (= s1_q2 (+ s1_q1 (* queue_data_rate t2))))))
(assert(= b2 (- b1 (* battery_discharge_rate_hover t2))))
;program: empty queue till battery <= 4
(assert (=> (= choice 0) (and (< (+ s1_q2 p9) s2_q2))))
(assert (=> (= choice 1) (and (< (+ s2_q2 p9) s1_q2))))

;flying back
(assert(= x3 0))
(assert(= x3 (- x2 (* drone_velocity t3))))
(assert(= s1_q3 (+ s1_q2 (* queue_data_rate t3))))
(assert(= s2_q3 (+ s2_q2 (* queue_data_rate t3))))
(assert(= b3 (- b2 (* battery_discharge_rate_fly t3))))

;goal
;Question: Does there exist starting battery,queue values such that safety is not maintained
; that is not (invariant => safety)
(assert (not (=> (or (and (>= bi p0) (<= s1_qi p1) (<= (+ s2_qi p2) s1_qi)) (and (>= bi p3) (<= (+ s1_qi p4) s2_qi) (<= s2_qi p5))) (and (> b0 0) (> b1 0) (> b2 0) (> b3 0) (< s1_q0 100) (< s1_q1 100) (< s1_q2 100) (< s1_q3 100) (< s2_q0 100) (< s2_q1 100) (< s2_q2 100) (< s2_q3 100) (or (and (>= b3 p0) (<= s1_q3 p1) (<= (+ s2_q3 p2) s1_q3)) (and (>= b3 p3) (<= (+ s1_q3 p4) s2_q3) (<= s2_q3 p5)))))))
(check-sat)
(exit)

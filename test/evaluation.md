# Size of state space
Tested w simple linear dynamics, start @ (5,50)
Delta-balls:
0.001 : unverifiable in 10 iterations, avg 17.656s
0.01: unverifiable in 10 iterations, avg 29.324s
0.1: unverifiable, avg 83.975s
1.0: unverifiable (b-init 5.0), avg 37.075s

# Environment dimension
Averaged over 10 runs. Starting (90,10)
10: 3 iterations, 0.483s
20: 3 iterations, 0.467s
30: 2 iterations, 0.274s
40: 4 iterations, 0.742s
50: 3 iterations, 0.446s
60: 4 iterations, 0.756s
70: 3 iterations, 0.506s
80: 4 iterations, 0.782s
90: unverifiable, 12.781s
100: unverifiable, 24.325s
1000: timeout


# Initial points
It's like impossible to get any useful metrics here.

# Complexity of dynamics

### Linear dynamics
Stats: 10 reps, avg: 0.472s, verified in 3 iterations

;charging
(assert(= x0 0))
(assert(= b0 (+ bi (* battery_charging_rate t0))))
(assert(= q0 (+ qi (* queue_data_rate t0))))
;program: charge till battery >= 20
(assert (=> (>= bi p2) (= b0 bi)))
(assert (or (=> (< bi p2) (= b0 p2)) (= q0 100)))

;flying to D
(assert(= x1 10))
(assert(= x1 (+ x0 (* drone_velocity t1))))
(assert(= b1 (- b0 (* battery_discharge_rate_fly t1))))
(assert(= q1 (+ q0 (* queue_data_rate t1))))

;emptying queue
(assert(= x2 10))
(assert(= q2 (- q1 (* queue_upload_rate t2))))
(assert(= b2 (- b1 (* battery_discharge_rate_hover t2))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1 p3) (= b2 p3)) (= q2 0)))
(assert (=> (<= b1 p3) (= b2 b1)))

;flying back
(assert(= x3 0))
(assert(= x3 (- x2 (* drone_velocity t3))))
(assert(= q3 (+ q2 (* queue_data_rate t3))))
(assert(= b3 (- b2 (* battery_discharge_rate_fly t3))))

### Polynomial dynamics
Stats: 10 reps, avg: 5.176, verified in 5 iterations

;charging
(assert(= x0 0))
(assert(= b0 (+ bi (* battery_charging_rate t0 t0))))
(assert(= q0 (+ qi (* queue_data_rate t0))))
;program: charge till battery >= 20
(assert (=> (>= bi p2) (= b0 bi)))
(assert (or (=> (< bi p2) (= b0 p2)) (= q0 100)))

;flying to D
(assert(= x1 10))
(assert(= x1 (+ x0 (* drone_velocity t1))))
(assert(= b1 (- b0 (* battery_discharge_rate_fly t1 t1))))
(assert(= q1 (+ q0 (* queue_data_rate t1))))

;emptying queue
(assert(= x2 10))
(assert(= q2 (- q1 (* queue_upload_rate t2))))
(assert(= b2 (- b1 (* battery_discharge_rate_hover t2))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1 p3) (= b2 p3)) (= q2 0)))
(assert (=> (<= b1 p3) (= b2 b1)))

;flying back
(assert(= x3 0))
(assert(= x3 (- x2 (* drone_velocity t3))))
(assert(= q3 (+ q2 (* queue_data_rate t3))))
(assert(= b3 (- b2 (* battery_discharge_rate_fly t3))))

### Transcendental dynamics
Stats: 10 reps, avg: 18.068s, verified in 1 iteration

start from (5, 50, 10, 1)

;charging
(assert (= x0 0))
(assert (= b0 (- (+ bi (* battery_charging_rate t0) (* 1 (cos t0))))))
(assert (= q0 (- (+ qi (* queue_data_rate t0)) (* 1 (cos t0)))))
;program: charge till battery >= 20
(assert (=> (>= bi p2) (= b0 bi)))
(assert (or (=> (< bi p2) (= b0 p2)) (= q0 100)))

;flying to D
(assert (= x1 10))
(assert (= x1 (- (+ x0 (* drone_velocity t1)) (* 5 (cos t1)))))
(assert (= b1 (+ (- b0 (* battery_discharge_rate_fly t1)) (* 5 (cos t1)))))
(assert (= q1 (- (+ q0 (* queue_data_rate t1)) (* 5 (cos t1)))))


;emptying queue
(assert (= x2 10))
(assert (= q2 (- (- q1 (* queue_upload_rate t2)) (* 5 (cos t2)))))
(assert (= b2 (- (- b1 (* battery_discharge_rate_hover t2)) (* 5 (cos t2)))))
;program: empty queue till battery <= 4
(assert (or (=> (> b1 p3) (= b2 p3)) (= q2 0)))
(assert (=> (<= b1 p3) (= b2 b1)))

;flying back
(assert(= x3 0))
(assert(= x3 (- x2 (* drone_velocity t3))))
(assert(= q3 (+ q2 (* queue_data_rate t3))))
(assert(= b3 (- b2 (* battery_discharge_rate_fly t3))))

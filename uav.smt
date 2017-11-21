x0
x1
x2
x3

bi
b0
b1
b2
b3

qi
q1
q2
q3

t0
t1
t2
t3

bi,qi belong to C

#charging
x0 = 0;
b0 = bi + rb*t0
q0 = qi + rq*t0
p: 90<= b0 <=100 

#flying to D
x1=xs
x1=x0 + v*t1
b1=b0 - rb*t1
q1=q0 + rq*t1

#emptying queue
x2=xs
q2=q1 - rq*t2
b2=b1 - rb*t2
p: 0<= q2 <20

#flying back
x3= 0
x3 = x2 - v*t3
q3=q2 + rq*t3
b3=b2 - rb*t3 

Check:
OR b0,b1,b2,b3 <= 0, q0,q1,q2,q3 >= 100 b3,q3 not(C)
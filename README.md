# Reactive UAV control

Program synthesis for hybrid systems.


To build: ` stack build`


To run: `stack exec -- uav [args]`


To run with the included example SMT templates: `stack exec -- uav smt/uav_dreal`


Currently supports [dReal](http://dreal.github.io/) versions 3 and 4. Configure the solver in `config/solver.cfg`.


TODO:
command line flag for 1-to-1 UAVs to sensors?

How to specify position while charging/collecting?

# Reactive UAV control

Dafny and Dreach scripts to verify reactive uav control


To build: ` stack build`


To run: `stack exec -- uav [filename] [num]` where filename is the prefix of the smt complete and template files, and num is an optional argument specifying the number of iterations for the loop invariant synthesis algorithm. 

:- use_module(library(lists)).
:- use_module('../src/clpfd_smt_interface').
:- use_module(library(clpfd)).


/*
 LIA MUCH FASTER THAN QF_FD!
 
 Results:
 ?- main.
 clpfd: 
 program, labeling, option
 0.013, 0.675, enum
 0.013, 0.745, ffc
 0.013, 0.329, bisect

 Z3, QF_FD:
 program, compilation, labeling
 0.008, 0.005, 22.562

 Z3, LIA
 program, compilation, labeling
 0.008, 0.005, 0.021
 0.008, 0.005, 0.013

*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

thedata([2,4,8,16,32,64,128,256,512,1024],
	[2,5,11,23,47,95,191,383,767,1535]).
            
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


main(Logic) :- 
	z3_init,
	statistics(runtime, [T0, _]),
	knapsack(1023, 1524, VarsR),
	statistics(runtime, [T1, _]),
	format('knapsack_z3 program execution took ~3d seconds\n', [T1-T0]),

	statistics(runtime, [P0, _]),
	z3_labeling([logic(Logic)],VarsR),!,
	statistics(runtime, [P1, _]),
	format('knapsack_z3 labeling took ~3d seconds\n', [P1-P0]),
	z3_stop,
	reverse(VarsR, Vars),
	write(Vars),
	nl.

knapsack(Space,Profit, VarsR) :-
    thedata(Weights,Costs),
	length(Weights,N),
	length(Vars,N),
    to_smtlib([
    	domain(Vars,0,Space),
    	scalar_product(Weights,Vars,#=<,Space),
    	scalar_product(Costs,Vars,#>=,Profit)
	]),
    reverse(Vars,VarsR).


main_clpfd :- 
	statistics(runtime, [T0, _]),
	knapsack_clpfd(1023, 1524, VarsR),
	statistics(runtime, [T1, _]),
	format('knapsack_clpfd program execution took ~3d seconds\n', [T1-T0]),

	statistics(runtime, [P0, _]),
	labeling([bisect],VarsR),!,
	statistics(runtime, [P1, _]),
	format('knapsack_clpfd labeling took ~3d seconds\n', [P1-P0]),
	reverse(VarsR, Vars),
	write(Vars),
	nl.



knapsack_clpfd(Space,Profit, VarsR) :-
	
    thedata(Weights,Costs),
    length(Weights,N),
    length(Vars,N),
    domain(Vars,0,Space),
    scalar_product(Weights,Vars,#=<,Space),
    scalar_product(Costs,Vars,#>=,Profit),
    reverse(Vars,VarsR).
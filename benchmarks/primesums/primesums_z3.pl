:- module(primesums, [main/0, main_findall/2, loop/3, primesums/2]).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module('../../src/clpfd_smt_interface').

/* Fill an NxN square with integers 1..n such that the sum of every
   row and column is a prime number. */


% ?- main. 
% => calculates one solution for primesums range 2x2,...,20x20.

main :- 
	set_prolog_flag(gc, off),
	(	count(I, 2, 20),
		foreach((I, P, L), Runtimes)
	do	loop(I, P, L), format('~d, ~3d, ~3d\n', [I,P,L])
	),
	write('N, Program_runtime, Labeling_runtime'),nl,
	(	foreach((I,P,L), Runtimes)
	do	format('~d, ~3d, ~3d\n', [I,P,L])
	).

% ?- main_findall(4, L).
% L = 1313923. (1.3 million)
main_findall(N, Number_of_Sols) :- 
	z3_init,
	statistics(runtime, [P0,_]),
	primesums(N, Vars),
	statistics(runtime, [P1,_]),
	format('execution of primesums took ~3d seconds\n', [P1-P0]),

	statistics(runtime, [T0,_]),
	findall(_X, z3_labeling([logic('LIA')], Vars), Xs),
	statistics(runtime, [T1,_]),
	format('primesums_z3 findall for ~d took ~3d seconds', [N, T1-T0]),
	
	length(Xs, Number_of_Sols),
	
	z3_stop.

% loop(20, P, L).
loop(N, Program_Runtime, Labeling_runtime) :-
	z3_reset,
	statistics(runtime, [Program0, _]),
	primesums(N, Vars),
	statistics(runtime, [Program1, _]),
	Program_Runtime is Program1-Program0,

	statistics(runtime, [Labeling0, _]),
    z3_labeling([logic('LIA')], Vars),
	statistics(runtime, [Labeling1, _]),
	Labeling_runtime is Labeling1-Labeling0,

	true.


primesums(Side, List) :-
        Side > 1,
	(   for(_,1,Side),
	    foreach(Row1,Rows),
	    fromto(Fmts,["~t~w,~6+"|Tail],Tail,["~n~n"]),
	    param(Side)
	do  length(Row1,Side)	    
	),
	append(Fmts, Fmt),
	append(Rows, List),
        Square is Side*Side,
        to_smtlib([
			domain(List, 1, Square),
        	all_distinct(List)
		]),
	(   for(J,2,Side*Side*Side),
	    foreach(J,S)
	do  true
	),
	(   fromto(S,[P|S1],S2,[]),
	    foreach(P,Primes)
	do  (   foreach(Y,S1),
		fromto(S2,T1,T2,[]),
		param(P)
	    do  (Y mod P > 0 -> T1 = [Y|T2] ; T1 = T2)
	    )
	),
	list_to_fdset(Primes, Fdset),
        transpose(Rows, Cols),
	Rows = [[R11,R12|R1s]|_],
	Cols = [[C11,C12|C1s]|_],
	to_smtlib([
		R12 #< C12
	]),
	(   foreach(Ry,[R12|R1s]),
	    fromto(R11,Rx,Ry,_),
	    foreach(Cy,[C12|C1s]),
	    fromto(C11,Cx,Cy,_)
	do  to_smtlib([
			Rx #< Ry,
	    	Cx #< Cy
		])
	),
	
	(   foreach(Row2,Rows),
	    foreach(Col,Cols),
	    param(Fdset)
	do  
	    to_smtlib([
			Sum1 in_set Fdset,
		    Sum2 in_set Fdset,
			sum(Row2, #=, Sum1),
	    	sum(Col, #=, Sum2)
		])
	),
	/*
		smtlib2_file([logic('LIA')], List, 'ps.smt2'),
		%z3_labeling([logic('LIA')], List),
		(   foreach(Row3,Rows),
			param(Fmt)
		do  format(Fmt, Row3)
		),
	*/
	true.

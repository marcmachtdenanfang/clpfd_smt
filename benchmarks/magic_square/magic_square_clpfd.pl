/*-------------------------------------------------------------------------*/
/* Benchmark (Finite Domain)            SICStus Prolog                     */
/*                                                                         */
/* Name           : magicsq.pl                                             */
/* Title          : magic squares                                          */
/* Author         : Mats Carlsson                                          */
/* Date           : January 2002                                           */
/*                                                                         */
/* In a magic square, the elements are all different, and the sum of each  */
/* column, each row, and main diagonal, are all the same.                  */
/*                                                                         */
/* Solution:                                                               */
/* N=4  [1,2,15,16,12,14,3,5,13,7,10,4,8,11,6,9]                           */
/* N=5  [1,2,13,24,25,3,22,19,6,15,23,16,10,11,5,21,7,9,20,8,17,18,14,4,12]*/
/*-------------------------------------------------------------------------*/

:- module(magicsq, [main/1, main_single/1, magic_square/3]).
:- use_module(library(lists)).
:- use_module(library(clpfd)).

% consistency: domain
% ?- main(4).
% Should return 1252 solutions
% Z3 takes roughly 60 seconds. program runtime 0.001 seconds, compilation 0.003 seconds.
% 2. program runtime=0.013, compilation=0.006, z3_labeling = 46.3-0.013-0.006
% 3. 53.556 seconds
% 4. 53 seconds
% z3
% CLPFD takes 1.06 seconds, program runtime 0.018 seconds. => labeling takes 1.04 seconds.

% ?- main_single(6). % finds a single solution for N
% 
% CLPFD returns solution in 0.035 seconds for N=6
% CLPFD returns solution in 3.277 seconds for N=5
% Z3    returns solution in an eternity for N=6, program runtime was 0.011 seconds, compilation was 0.006 seconds aka negligeable
% Z3    returns solution in 190   seconds for N=5 program runtime was 0.002 seconds, compilation was 0.004 seconds aka negligeable

% consistency: bound (slightly different constraints)
% ?- main_single(N)
% CLPFD returns solution in 0.035 seconds for N=6
% CLPFD returns solution in 3.277 seconds for N=5
% Z3    returns solution in an eternity for N=6, program runtime was 0.011 seconds, compilation was 0.006 seconds aka negligeable
% Z3    returns solution in 107.284 seconds for N=5 program runtime was 0.014 seconds, compilation was 0.006 seconds aka negligeable

main(N) :- 
	statistics(runtime, [T0,_]),
	
	findall(Vars, magic_square([ff,bisect], N, domain, Vars), L),
    length(L, NumOf6),
    format('There are ~d magic squares.\n', [NumOf6]),

	statistics(runtime, [T1,_]),
	format('magic square in clpfd\n', []),
	format('Solving for all solutions of N=~d took ~3d seconds\n', [N, T1-T0]).

main_single(N) :- 
	statistics(runtime, [T0,_]),
	
	magic_square([ff,bisect], N, domain, Vars),

	statistics(runtime, [T1,_]),
	format('magic square in clpfd\n', []),
	format('Solving for one solution of N=~d took ~3d seconds\n', [N,T1-T0]),

	%format('Magic ~d x ~d square:\n', [N,N]),
	%fmt(N, Fmt, []),
	%(   fromto(Vars,S0,S,[]),
	%    param([N,Fmt])
	%do  (   for(_,1,N),
	%	fromto(S0,[X|S1],S1,S),
	%	fromto(Row,[X|R],R,[])
	%    do  true
	%    ),
	%    format(Fmt, Row)
	%),
	true.


magic_square(Lab, N, Consistency, Vars) :-
    statistics(runtime, [T0,_]),
	
	Opt = [consistency(Consistency)],
    problem(N, Vars, Opt),
	
    statistics(runtime, [T1,_]),
	format('Program runtime took ~3d seconds\n', [T1-T0]),

	labeling(Lab, Vars),
	/*format('Magic ~d x ~d square:\n', [N,N]),
	fmt(N, Fmt, []),
	(   fromto(Vars,S0,S,[]),
	    param([N,Fmt])
	do  (   for(_,1,N),
		fromto(S0,[X|S1],S1,S),
		fromto(Row,[X|R],R,[])
	    do  true
	    ),
	    format(Fmt, Row)
	),*/
    true.

fmt(0) --> !, "\n".
fmt(I) --> "~t~d~+",
	{J is I-1},
	fmt(J).

/*
system(3, Vars) :-
	Vars = [X1,X2,X3,X4,X5,X6,X7,X8,X9],
	domain(Vars, 1, 9),
	all_different(Vars),
	X1+X2+X3#=15,
	X4+X5+X6#=15,
	X7+X8+X9#=15,
	X1+X4+X7#=15,
	X2+X5+X8#=15,
	X3+X6+X9#=15,
	X1+X5+X9#=15,
	X3+X5+X7#=15.
system(4, Vars) :-
	Vars = [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12,X13,X14,X15,X16],
	domain(Vars, 1, 16),
	all_different(Vars),
	X1+X2+X3+X4#=34,
	X5+X6+X7+X8#=34,
	X9+X10+X11+X12#=34,
	X13+X14+X15+X16#=34,
	X1+X5+X9+X13#=34,
	X2+X6+X10+X14#=34,
	X3+X7+X11+X15#=34,
	X4+X8+X12+X16#=34,
	X1+X6+X11+X16#=34,
	X4+X7+X10+X13#=34.
*/

problem(N, Square, [consistency(domain)]) :- !,
	NN is N*N,
	length(Square0, NN),
	domain(Square0, 1, NN),
	sort(Square0, Square),
	all_different(Square, [consistency(domain)]),
	Sum is (N*(NN+1))>>1,
	/* essential constraints */
	rows(0, N, Square, Ss, Ss1),
	columns(0, N, Square, Ss1, [SO,SW]),
	Nup is N+1,
	elts(N, 1, Nup, Square, SO),
	Ndown is N-1,
	elts(N, N, Ndown, Square, SW),
	(   foreach(S,Ss),
	    param(Sum)
	do  (   foreach(_,S),
		foreach(1,One)
	    do  true
	    ),
	    scalar_product(One, S, #=, Sum, [consistency(domain)])
	),
	/* symmetry breaking constraints */
	nth1(1, Square, X11),
	NNdown is NN-Ndown,
	nth1(NNdown, Square, XN1),
	nth1(N, Square, X1N),
	X11 #> X1N,
	X1N #> XN1,
	true.
problem(N, Square, [consistency(bound)]) :- !,
	NN is N*N,
	length(Square0, NN),
	domain(Square0, 1, NN),
	sort(Square0, Square),
	Sum is (N*(NN+1))>>1,
	/* essential constraints */
	rows(0, N, Square, Ss, Ss1),
	columns(0, N, Square, Ss1, [SO,SW]),
	Nup is N+1,
	elts(N, 1, Nup, Square, SO),
	Ndown is N-1,
	elts(N, N, Ndown, Square, SW),
	(   foreach(S,Ss),
	    foreach(Expr #= Sum,Eqs),
	    param(Sum)
	do  plusify(S, Expr)
	),
	all_different(Square, Eqs),
	/* symmetry breaking constraints */
	nth1(1, Square, X11),
	NNdown is NN-Ndown,
	nth1(NNdown, Square, XN1),
	nth1(N, Square, X1N),
	X11 #> X1N,
	X1N #> XN1,
	true.

plusify([], 0).
plusify([P|Ps], Conj) :-
	plusify(Ps, P, Conj).

plusify([], P, P).
plusify([P|Ps], Q, Conj) :-
	plusify(Ps, Q+P, Conj).

rows(N, N, _) --> !.
rows(I, N, L) --> [Row],
	{J is I+1,
	 Start is I*N+1,
	 elts(N, Start, 1, L, Row)},
	rows(J, N, L).

columns(N, N, _) --> !.
columns(I, N, L) --> [Column],
	{J is I+1,
	 elts(N, J, N, L, Column)},
	columns(J, N, L).

elts(0, _, _, _, []) :-!.
elts(J, Index, Step, L, [X|Xs]) :-
	nth1(Index, L, X),
	I is J-1,
	Jndex is Index+Step,
	elts(I, Jndex, Step, L, Xs).
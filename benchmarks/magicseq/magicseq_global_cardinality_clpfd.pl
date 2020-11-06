/*-------------------------------------------------------------------------*/
/* Benchmark (Finite Domain)            INRIA Rocquencourt - ChLoE Project */
/*                                                                         */
/* Name           : magic.pl                                               */
/* Title          : magic series                                           */
/* Original Source: W.J. Older and F. Benhamou - Programming in CLP(BNR)   */
/*                  (in Position Papers of PPCP'93)                        */
/* Adapted by     : Daniel Diaz - INRIA France                             */
/* Date           : May 1993                                               */
/*                                                                         */
/* A magic serie is a sequence x0, x1, ..., xN-1 such that each xi is the  */
/* number of occurences of i in the serie.                                 */
/*           N-1                                                           */
/*  ie  xi = Sum (xj=i)  where (xj=i) is 1 if x=y and 0 if x<>y            */
/*           i=0                                                           */
/*                                                                         */
/* two redundant constraints are used:                                     */
/*           N-1                     N-1                                   */
/*           Sum i = N          and  Sum i*xi = N                          */
/*           i=0                     i=0                                   */
/*                                                                         */
/* Note: in the Pascal's original version the length of a magic serie is   */
/* N+1 (x0, x1, ..., XN) instead of N (x0, x1, ..., xN-1). Finding such a  */
/* serie (for N) only corresponds to find a serie for N+1 in this version. */
/* Also the original version only used one redundant constraint.           */
/*                                                                         */
/* Solution:                                                               */
/* N=1,2,3 and 6 none                                                      */
/* N=4  [1,2,1,0] and [2,0,2,0]                                            */
/* N=5  [2,1,2,0,0]                                                        */
/* N=7  [3,2,1,1,0,0,0]   (for N>=7  [N-4,2,1,<N-7 0's>,1,0,0,0])          */
/*-------------------------------------------------------------------------*/

:- module(magic, [main/0, magic/3, magic_demo/2]).
:- use_module(library(clpfd)).


main :- 
	statistics(runtime, [T40,_]),
	magic_demo(4, Sol4),
	statistics(runtime, [T41,_]),
	statistics(runtime, [L40,_]),
	findall(Sol4, labeling([enum], Sol4), _),
	statistics(runtime, [L41,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [4, T41-T40, L41-L40]),

	statistics(runtime, [T50,_]),
	magic_demo(5, Sol5),
	statistics(runtime, [T51,_]),
	statistics(runtime, [L50,_]),
	labeling([enum], Sol5),	% there is only a single solution
	statistics(runtime, [L51,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [5, T51-T50, L51-L50]),

	statistics(runtime, [T70,_]),
	magic_demo(7, Sol7),
	statistics(runtime, [T71,_]),
	statistics(runtime, [L70,_]),
	labeling([enum], Sol7),
	statistics(runtime, [L71,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [7, T71-T70, L71-L70]),

	statistics(runtime, [T100,_]),
	magic_demo(10, Sol10),
	statistics(runtime, [T101,_]),
	statistics(runtime, [L100,_]),
	labeling([enum], Sol10),
	statistics(runtime, [L101,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [10, T101-T100, L101-L100]),

	statistics(runtime, [T180,_]),
	magic_demo(18, Sol18),
	statistics(runtime, [T181,_]),
	statistics(runtime, [L180,_]),
	labeling([enum], Sol18),
	statistics(runtime, [L181,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [18, T181-T180, L181-L180]),

	statistics(runtime, [T300,_]),
	magic_demo(30, Sol30),
	statistics(runtime, [T301,_]),
	statistics(runtime, [L300,_]),
	labeling([enum], Sol30),
	statistics(runtime, [L301,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [30, T301-T300, L301-L300]),

	%findall(Sol, magic_demo(5, Sol), _),
	%findall(Sol, magic_demo(7, Sol), _),
	%findall(Sol, magic_demo(10, Sol), _),
	%findall(Sol, magic_demo(20, Sol), _),
	%findall(Sol, magic_demo(30, Sol), _),
	true.

% for FDBG example
magic_demo(N, L) :-
	length(L, N),
	N1 is N-1,
	domain(L, 0, N1),
	constraints(L, domain),
	%labeling([enum], L),
	true.

magic(N, Lab, Cons) :-
	length(L, N),
	N1 is N-1,
	domain(L, 0, N1),
	constraints(L, Cons),
	labeling(Lab, L),
	writeq(L),
	nl.

constraints(Vars, Cons) :-
	(   foreach(X,Vars),
	    foreach(I-X,Pairs),
	    count(I,0,_)
	do  true
	),
	global_cardinality(Vars, Pairs, [consistency(Cons)]).
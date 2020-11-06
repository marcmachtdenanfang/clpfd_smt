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
% :- use_module(library(clpfd)).
:- use_module('../../src/clpfd_smt_interface.pl').

main :- 
	z3_init,
	set_prolog_flag(gc, off),


	statistics(runtime, [T40,_]),
	magic_demo(4, Sol4),
	statistics(runtime, [T41,_]),
	statistics(runtime, [L40,_]),
	findall(Sol4, z3_labeling([logic('LIA')], Sol4), _),
	statistics(runtime, [L41,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [4, T41-T40, L41-L40]),

	z3_reset,

	statistics(runtime, [T50,_]),
	magic_demo(5, Sol5),
	statistics(runtime, [T51,_]),
	statistics(runtime, [L50,_]),
	z3_labeling([logic('LIA')], Sol5),	% there is only a single solution
	statistics(runtime, [L51,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [5, T51-T50, L51-L50]),

	z3_reset,

	statistics(runtime, [T70,_]),
	magic_demo(7, Sol7),
	statistics(runtime, [T71,_]),
	statistics(runtime, [L70,_]),
	z3_labeling([logic('LIA')], Sol7),
	statistics(runtime, [L71,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [7, T71-T70, L71-L70]),

	z3_reset,

	statistics(runtime, [T100,_]),
	magic_demo(10, Sol10),
	statistics(runtime, [T101,_]),
	statistics(runtime, [L100,_]),
	z3_labeling([logic('LIA')], Sol10),
	statistics(runtime, [L101,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [10, T101-T100, L101-L100]),

	z3_reset,

	statistics(runtime, [T180,_]),
	magic_demo(18, Sol18),
	statistics(runtime, [T181,_]),
	statistics(runtime, [L180,_]),
	z3_labeling([logic('LIA')], Sol18),
	statistics(runtime, [L181,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [18, T181-T180, L181-L180]),

	z3_reset,

	statistics(runtime, [T300,_]),
	magic_demo(30, Sol30),
	statistics(runtime, [T301,_]),
	statistics(runtime, [L300,_]),
	z3_labeling([logic('LIA')], Sol30),
	statistics(runtime, [L301,_]),
	format('Solving for N=~d, runtime:~3d, labeling:~3d\n', [30, T301-T300, L301-L300]),

	z3_stop.

	%statistics(runtime, [A0,_]),
	%statistics(runtime, [T0,_]),
	%findall(Sol, magic_demo(4, Sol), _),
	%statistics(runtime, [T1,_]),
	%statistics(runtime, [T01,_]),
	%findall(Sol, magic_demo(5, Sol), _),
	%statistics(runtime, [T11,_]),
	%z3_reset,
	%statistics(runtime, [T02,_]),
	%findall(Sol, magic_demo(7, Sol), _),
	%statistics(runtime, [T12,_]),
	%z3_reset,
	%statistics(runtime, [T21,_]),
	%findall(Sol, magic_demo(10, Sol), _),
	%statistics(runtime, [T22,_]),
	%z3_reset,
	% % The next two take very long in Z3, not in CLPFD.
	%
	%statistics(runtime, [T30,_]),
	%findall(Sol, magic_demo(18, Sol), _),
	%statistics(runtime, [T31,_]),
	%/*
	%z3_reset,
	%findall(Sol, magic_demo(30, Sol), _),
	%*/
	%format('1, ~3d\n2, ~3d\n3, ~3d\n4, ~3d\n5, ~3d', [T1-T0, T11-T01,T12-T02,T22-T21,T31-T30]),
	%statistics(runtime, [A1,_]),
	%format('magicseq using global_cardinality in Z3\n', []),
	%format('Solving for N=4,5,7,10,18 took ~3d seconds\n', [A1-A0]),
	%z3_stop.

% for FDBG example
magic_demo(N, L) :-
	length(L, N),
	N1 is N-1,
	to_smtlib([
		domain(L, 0, N1)
	]),
	constraints(L, domain),
	%z3_labeling([logic('QF_FD')], L).
	true.

constraints(Vars, Cons) :-
	(   foreach(X,Vars),
	    foreach(I-X,Pairs),
	    count(I,0,_)
	do  true
	),
	to_smtlib([
		global_cardinality(Vars, Pairs, [consistency(Cons)])
	]).
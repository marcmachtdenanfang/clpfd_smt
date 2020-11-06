:- module(hamming, [main/0, hamming/4]).
% ?- set_prolog_flag(gc, off), clpfd_z3:z3_init, hamming(10,5,9,_), z3_labeling([logic('QF_FD')], Vars), clpfd_z3:z3_stop.
% ?- set_prolog_flag(gc, off), clpfd_z3:z3_init, hamming(10,3,64,_), z3_labeling([logic('QF_FD')], Vars), clpfd_z3:z3_stop.

% ?- bench([hamming(10,3,64),hamming(10,5,9)]).

% :- use_module(library(clpfd)).
:- use_module('../../src/clpfd_smt_interface').
:- use_module(library(lists), [append/2,transpose/2]).

%%% Find a binary Hamming code (N,D) with K elements.
%%% K = #words
%%% N = word size
%%% D: sum of pairwise difference >= D

main :-
	z3_init,
	set_prolog_flag(gc, off),

	% This call does not currently terminate: hamming(10,3,64, Vars)
	% Needs to implement lex_chain for this CSP to improve performance.

	%statistics(runtime, [T0,_]),
	%hamming(10,3,64, Vars),
	%statistics(runtime, [T1,_]),
	%format('~3d seconds\n', [T1-T0]),
	%clpfd_smt_base:get_all_constraints(C),
	%length(C,L),
	%format('Length: ~d', [L]),
	%
	%statistics(runtime, [P0,_]),
	%z3_labeling([logic('QF_FD')], Vars), !,
	%statistics(runtime, [P1,_]),
	%format('1, ~3d, ~3d\n', [T1-T0, P1-P0]),
	%
	%z3_reset,

	statistics(runtime, [T01,_]),
	hamming(10,5,9, Vars1),
	statistics(runtime, [T11,_]),
	
	statistics(runtime, [P01,_]),
	z3_labeling([logic('QF_FD')], Vars1), !,
	statistics(runtime, [P11,_]),
	
	clpfd_smt_base:get_all_constraints(C),
	length(C,L),
	format('Length: ~d', [L]),
	

	write('hamming_z3, QF_FD\n'),
	write('ID, execution, labeling\n'),
	format('2, ~3d, ~3d', [T11-T01, P11-P01]),
	
	z3_stop.

	

hamming(N, D, K, Vars) :-
	length(Words, K),
	(   foreach(Word1,Words),
	    param(N)
	do  length(Word1, N),
	    to_smtlib([domain(Word1, 0, 1)])
	),
	Words = [Head|_],
	transpose(Words, Columns),
	to_smtlib([
		domain(Head, 0, 0),
		%lex_chain(Words, [op(#<)]),
		lex_chain(Words),
		lex_chain(Columns)
	]),
	(   fromto(Words,[Word2|Rest],Rest,[]),
	    param(D)
	do  (   foreach(Word3,Rest),
		param([Word2,D])
	    do  (   foreach(A,Word3),
		    foreach(B,Word2),
		    foreach(C,Cs)
		do  %to_smtlib([bool_xor([A,B], C)]) % ok
			%! not ok: to_smtlib([(A #\ B) #<=> C])
			to_smtlib([(A#=1 #\ B#=1) #<=> C]) % ok
		),
		to_smtlib([sum(Cs, #>=, D)])
	    )
	),
	append(Words, Vars),
	
	
	z3_labeling([], Vars),
	(   foreach(Row,Words)
	do  (   foreach(R,Row),
		foreach(S,String)
	    do  S is R+"0"
	    ),
	    format('~s\n', [String])
	),
	
	true.

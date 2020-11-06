:- module(hamming, [main/0, hamming/3]).

% ?- bench([hamming(10,3,64),hamming(10,5,9)]).

:- use_module(library(clpfd)).
:- use_module(library(lists), [append/2,transpose/2]).

%%% Find a binary Hamming code (N,D) with K elements.
%%% K = #words
%%% N = word size
%%% D: sum of pairwise difference >= D

main :-
	statistics(runtime, [T0,_]),
	hamming(10,3,64, Vars),
	statistics(runtime, [T1,_]),
	statistics(runtime, [P0,_]),
	labeling([], Vars), !,
	statistics(runtime, [P1,_]),
	
	statistics(runtime, [T01,_]),
	hamming(10,5,9, Vars1),
	statistics(runtime, [T11,_]),
	statistics(runtime, [P01,_]),
	labeling([], Vars1), !,
	statistics(runtime, [P11,_]),
	write('hamming_clpfd\n'),
	write('ID, execution, labeling\n'),
	format('1, ~3d, ~3d\n', [T1-T0, P1-P0]),
	format('2, ~3d, ~3d', [T11-T01, P11-P01]).

	

hamming(N, D, K, Vars) :-
	length(Words, K),
	(   foreach(Word1,Words),
	    param(N)
	do  length(Word1, N),
	    domain(Word1, 0, 1)
	),
	Words = [Head|_],
	domain(Head, 0, 0),
	lex_chain(Words, [op(#<)]),
	transpose(Words, Columns),
	lex_chain(Columns),
	(   fromto(Words,[Word2|Rest],Rest,[]),
	    param(D)
	do  (   foreach(Word3,Rest),
		param([Word2,D])
	    do  (   foreach(A,Word3),
		    foreach(B,Word2),
		    foreach(C,Cs)
		do  (A #\ B) #<=> C
		),
		sum(Cs, #>=, D)
	    )
	),
	append(Words, Vars),
	/*
	labeling([], Vars), !,
	(   foreach(Row,Words)
	do  (   foreach(R,Row),
		foreach(S,String)
	    do  S is R+"0"
	    ),
	    format('~s\n', [String])
	),
	*/
	true.

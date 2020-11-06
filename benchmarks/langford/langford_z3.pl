% % Langford's Problem  (CSPlib problem 24)
% %
% % June 2006; Sebastian Brand
% %
% % Instance L(k,n):
% % Arrange k sets of numbers 1 to n so that each appearance of the number m is m
% % numbers on from the last.  For example, the L(3,9) problem is to arrange 3
% % sets of the numbers 1 to 9 so that the first two 1's and the second two 1's
% % appear one number apart, the first two 2's and the second two 2's appear two
% % numbers apart, etc.
% %-----------------------------------------------------------------------------%
% % MiniZinc version
% % Peter Stuckey September 30

% include "globals.mzn";

% %-----------------------------------------------------------------------------%
% % Instance
% %-----------------------------------------------------------------------------%

% int: n = 9;
% int: k = 3;

% %-----------------------------------------------------------------------------%
% % Input
% %-----------------------------------------------------------------------------%

% set of int: numbers = 1..n;             % numbers
% set of int: sets    = 1..k;             % sets of numbers
% set of int: num_set = 1..n*k;

% set of int: positions = 1..n*k;         % positions of (number, set) pairs

% %-----------------------------------------------------------------------------%
% % Primal model
% %-----------------------------------------------------------------------------%

% array[num_set] of var positions: Pos;
% 					% Pos[ns]: position of (number, set)
%                                         % pair in the sought sequence
% constraint
%         forall(i in 1..n, j in 1..k-1) (
%             Pos[k*(i-1) + j+1] - Pos[k*(i-1) + j] = i+1
%         );

% constraint
%         alldifferent(Pos);

% %-----------------------------------------------------------------------------%
% % Dual model (partial)
% %-----------------------------------------------------------------------------%

% array[positions] of var num_set: Num;   % Num[p]: (number, set) pair at
%                                         % position p in the sought sequence
% constraint
%         alldifferent(Num);

% %-----------------------------------------------------------------------------%
% % Channelling between primal model and dual model
% %-----------------------------------------------------------------------------%

% constraint
%         forall(i in numbers, j in sets, p in positions) (
%                 (Pos[k*(i-1) + j] = p) <-> (Num[p] = k*(i-1) + j)
%         );

% %-----------------------------------------------------------------------------%

% 	% Without specifying a sensible search order this problem takes
% 	% forever to solve.
% 	%
% solve	:: int_search(Pos, first_fail, indomain_split, complete)
% 	satisfy;

% output
% 	[ if j = 1 then "\n" ++ show(i) ++ "s at " else ", " endif ++
% 	  show(Pos[k*(i-1) + j])
% 	| i in 1..n, j in 1..k
% 	] ++
% 	[ "\n" ];

:- module(langford, [main/0, langford/2]).
:- use_module(library(lists)).
% :- use_module(library(clpfd)).
:- use_module('../../src/clpfd_smt_interface').


% For langford(3, 10).
% Finding all solutions with Z3: Öfters 11,8 bzw. 11,9 sekunden als 14 sekunden
% 14,419 sekunden, 11,972 sekunden (fresh start!), 13,988 sekunden (with cache)
% Finding all solutions with clpfd: 5,681 sekunden
% If clpfd uses bool_channel instead of assignment: 15,523 sekunden
%
% After changes to the system, constraints with reified variables are no hindrance
% to use QF_FD.
% Performance is good.
% Takes 2.088, 2.149, 2.535 seconds with QF_FD, to find all ten solutions.
% If clpfd uses ffc over the original recommended strategies, and assignment, it takes 
% 0.079 seconds to find all 10 solutions. 0.086 seconds with bool_channel.

main :-
    set_prolog_flag(gc, off),
    z3_init,
    statistics(runtime,[T0,_]), 
    
    langford(3,10),
    
    statistics(runtime,[T1,_]),
    format('langford_z3 took ~3d seconds\n',[T1-T0]),

    z3_reset.

langford(K, N) :-
	NK is N*K,
	length(Pos, NK),
	to_smtlib([domain(Pos, 1, NK)]),
    % Pos[ns]: position of (number, set)
	% pair in the sought sequence
	(   for(I,1,N),
	    param(K,Pos)
	do  (   for(J,1,K-1),
		param(I,K,Pos)
	    do  Ix1 is K*(I-1) + J+1,
		Ix2 is Ix1-1,
		I1 is I+1,
		nth1(Ix1, Pos, Pos1),
		nth1(Ix2, Pos, Pos2),
		to_smtlib([Pos1 - Pos2 #= I1])
	    )
	),
	length(Num, NK),
	to_smtlib([domain(Num, 1, NK)]),
    % Num[p]: (number, set) pair at
	% position p in the sought sequence
%	assignment(Pos, Num),
	% totally redundant, because of use of assignment:
	(   for(_,1,NK),
	    foreach(NumjEq,NumEq),
	    param(NK)
	do  length(NumjEq, NK)
	),
	transpose(NumEq, NumEqT),
%write(NumEq),
	(   foreach(Numi,Num),
	    foreach(NumiEq,NumEq),
	    foreach(Posi,Pos),
	    foreach(PosiEq,NumEqT)
	do  to_smtlib([
            bool_channel(NumiEq, Numi, #=, 1),
	        bool_channel(PosiEq, Posi, #=, 1)
        ])
	),
	
    append(Pos,Num, Vars),
    %smtlib2_file([], Vars, 'langford.smt2'),
	z3_labeling([min,bisect], Vars), % by trial and error
    %findall(Sol, z3_labeling([min, bisect, logic('QF_FD')], Vars),Sols),
    %length(Sols, NumOfSols),
    %write('Number of possible Solutions: '), write(NumOfSols),nl.
	format('~w\n~w\n', [Pos,Num]),
	(   for(I3,1,N),
	    fromto(Pos,Posa,Posb,[]),
	    param(K)
	do  length(Prefix, K),
	    append(Prefix, Posb, Posa),
	    format('Position of "~d": ~w\n', [I3,Prefix])
	).
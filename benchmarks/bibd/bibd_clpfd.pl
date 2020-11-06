/*
 * SICSTUS CLPFD DEMONSTRATION PROGRAM
 * Purpose   : Balanced Incomplete Block Design
 * Author    : Mats Carlsson
 *
 * The goal is to find a VxB binary matrix with
 * R ones in each row, K ones in each column,
 * the scalar product of any two rows being Lambda.
 */

/* ?- bench([bibd([rl,up,lex], 10, 90, 27, 3, 6),
	     bibd([rl,up,lex], 15, 70, 14, 3, 2),
	     bibd([rl,up,lex], 12, 88, 22, 3, 4),
	     bibd([rl,up,lex], 9, 120, 40, 3, 10),
	     bibd([rl,up,lex], 10, 120, 36, 3, 8),
	     bibd([rl,up,lex], 13, 104, 24, 3, 4)]).
*/

:- module(bibd, [main/0, bibd/6]).

:- use_module(library(lists), [
        reverse/2,
        transpose/2
	]).
:- use_module(library(clpfd)).

% 	bibd([rl,up,lex], 8, 14, 7, 4, 3).
% SUCCEEDS, 43 bks
% 	bibd([lr,down,antilex], 8, 14, 7, 4, 3).
% SUCCEEDS, 112 bks

% 	bibd([rl,up,lex], 6, 50, 25, 3, 10).
% SUCCEEDS, 143 bks
% 	bibd([lr,down,antilex], 6, 50, 25, 3, 10).
% SUCCEEDS, 180 bks

% 	bibd([rl,up,lex], 6, 60, 30, 3, 12).
% SUCCEEDS, 205 bks
% 	bibd([lr,down,antilex], 6, 60, 30, 3, 12).
% SUCCEEDS, 276 bks

% 	bibd([rl,up,lex], 6, 70, 35, 3, 10).
% FAILS

% 	bibd([rl,up,lex], 10, 90, 27, 3, 6).
% SUCCEEDS, 450 bks
% 	bibd([lr,down,antilex], 10, 90, 27, 3, 6).
% SUCCEEDS, 482 bks

% 	bibd([rl,up,lex], 9, 108, 36, 3, 9).
% SUCCEEDS, 94694 bks
% 	bibd([lr,down,antilex], 9, 108, 36, 3, 9).
% SUCCEEDS, 90 bks

% 	bibd([rl,up,lex], 15, 70, 14, 3, 2).
% SUCCEEDS, 116 bks
% 	bibd([lr,down,antilex], 15, 70, 14, 3, 2).
% SUCCEEDS, 0 bks

% 	bibd([rl,up,lex], 12, 88, 22, 3, 4).
% SUCCEEDS, 290 bks
% 	bibd([lr,down,antilex], 12, 88, 22, 3, 4).
% SUCCEEDS, 7687 bks

% 	bibd([rl,up,lex], 9, 120, 40, 3, 10).
% SUCCEEDS, 305 bks
% 	bibd([lr,down,antilex], 9, 120, 40, 3, 10).
% SUCCEEDS, 110 bks

% 	bibd([rl,up,lex], 10, 120, 36, 3, 8).
% SUCCEEDS, 890 bks
% 	bibd([lr,down,antilex], 10, 120, 36, 3, 8).
% SUCCEEDS, 1202 bks

% 	bibd([rl,up,lex], 13, 104, 24, 3, 4).
% SUCCEEDS, 212 bks
% 	bibd([lr,down,antilex], 13, 104, 24, 3, 4).
% SUCCEEDS, 577 bks

% 	bibd([rl,up,lex], 22, 33, 12, 8, 4).
% OPEN INSTANCE, >6247634 bks
% 	bibd([lr,down,antilex], 22, 33, 12, 8, 4).
% OPEN INSTANCE, >6247634 bks

main :-
	write('Iteration, Execution Time, Labeling Time\n'),
	
	bibd([rl,up,lex], 8, 14, 7, 4, 3, V1, P1, L1),
	format('~d, ~3d, ~3d\n', [1, P1, L1]),
	
	bibd([rl,up,lex], 6, 50, 25, 3, 10, V2, P2,L2),
	format('~d, ~3d, ~3d\n', [1, P2, L2]),

	bibd([rl,up,lex], 6, 60, 30, 3, 12, V3,P3,L3),
	format('~d, ~3d, ~3d\n', [1, P3, L3]),

	bibd([rl,up,lex], 10, 90, 27, 3, 6, V4,P4,L4),
	format('~d, ~3d, ~3d\n', [1, P4, L4]),

	bibd([rl,up,lex], 9, 108, 36, 3, 9, V5,P5,L5),
	format('~d, ~3d, ~3d\n', [1, P5, L5]),

	bibd([rl,up,lex], 15, 70, 14, 3, 2, V6,P6,L6),
	format('~d, ~3d, ~3d\n', [1, P6, L6]),

	bibd([rl,up,lex], 12, 88, 22, 3, 4, V7,P7,L7),
	format('~d, ~3d, ~3d\n', [1, P7, L7]),

	bibd([rl,up,lex], 9, 120, 40, 3, 10, V8,P8,L8),
	format('~d, ~3d, ~3d\n', [1, P8, L8]),

	bibd([rl,up,lex], 10, 120, 36, 3, 8, V9,P9,L9),
	format('~d, ~3d, ~3d\n', [1, P9, L9]),

	bibd([rl,up,lex], 13, 104, 24, 3, 4, V10,P10,L10),
	format('~d, ~3d, ~3d\n', [1, P10, L10]),
	
    
    %bibd([rl,up,lex], 8, 14, 7, 4, 3),     % bibd_clpfd took 0.025 seconds
    % bibd([rl,up,lex], 15, 70, 14, 3, 2),    % bibd_clpfd took 0.070 seconds
    true.

bibd([Order,Lab,Lex], V, B, R, K, Lambda, Vars, Program_runtime, Labeling_Runtime) :-
	statistics(runtime, [P0,_]),
	bibd(Lex, V, B, R, K, Lambda, _Cells, Rows),
	bibd_order(Order, Rows, Vars),
	statistics(runtime, [P1,_]),
	
	statistics(runtime, [L0,_]),	
	labeling([Lab], Vars),
	statistics(runtime, [L1,_]),
	
	Program_runtime is P1-P0, 
	Labeling_Runtime is L1-L0,
	/*
		(   foreach(Row,Rows)
		do  (   foreach(R1,Row),
			foreach(S,String)
			do  S is R1+"0"
			),
			format('~s\n', [String])
		),
	*/
	true.

bibd_order(lr, Rows, Vars) :-
	(   foreach(Row,Rows),
	    fromto(Vars,S0,S,[])
	do  append(Row, S, S0)
	).
bibd_order(rl, Rows, Vars) :-
	(   foreach(Row,Rows),
	    fromto(Vars,S0,S,[])
	do  reverse(Row, Rev),
	    append(Rev, S, S0)
	).

bibd(Lex, V, B, R, K, Lambda, Cells, Rows) :-
	VC is V*B,
	length(Cells, VC),
	domain(Cells, 0, 1),
	(   fromto(Cells,C1,C3,[]),
	    foreach(Row1,Rows),
	    param(B)
	do  length(Row1, B),
	    (   foreach(Elt,Row1),
		fromto(C1,[Elt|C2],C2,C3)
	    do  true
	    )
	),
	transpose(Rows, Columns),
	(   Lex==lex ->
	    Rows = LexRows,
	    Columns = LexColumns
	;   reverse(Rows, LexRows),
	    reverse(Columns, LexColumns)
	),
	%lex_chain(LexRows, [op(#<)/*,among(R,R,[1])*/]),
	%lex_chain(LexColumns, [op(#=<)/*,among(K,K,[1])*/]),
	(   foreach(Row2,Rows),
	    param(R)
	do  sum(Row2, #=, R)
	),
	(   foreach(Col,Columns),
	    param(K)
	do  sum(Col, #=, K)
	),
	(   fromto(Rows,[Row0|Rest],Rest,[]),
	    param(Lambda)
	do  (   foreach(Row3,Rest),
		param([Row0,Lambda])
	    do  (   foreach(X,Row0),
		    foreach(Y,Row3),
		    foreach(Z,S)
		do  X #/\ Y #<=> Z
		),
		sum(S, #=, Lambda)
	    )
	).
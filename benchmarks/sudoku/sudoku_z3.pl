:- use_module(library(clpfd)).
:- use_module(library(lists)).
:- use_module(library(plunit)).
:- use_module('../../src/clpfd_smt_interface').

/* Generalized Sudoku. */
solve_sudoku(Rows, Rows) :-
    z3_reset,
    set_prolog_flag(gc,off),
    
    Rows = [Row|_],
    length(Row, N),
    append(Rows,Flat),
    to_smtlib([
        domain(Flat,1,N)
    ]),
    constrain_squares(Rows,1,N,_Squares),
    transpose(Rows,Columns),
    to_smtlib([
        maplist(all_distinct,Rows),
        maplist(all_different,Columns)
    ]),
    z3_labeling([logic('QF_FD')],Flat),
    %print_sudoku(Rows),

    true.

constrain_squares([],_,_,[]).
constrain_squares(S,C,N,Square) :-
    X is sqrt(N),                       % sqrt(N)-Zeilen wegschneiden um Squares in
    X1 is ceiling(X),                   % naechster "Ebene" zu suchen, sobald
    C > X1,                             % die vorherige abgearbeitet ist.
    cut_list(S,X1,NS),
    constrain_squares(NS,1,N,Square).
constrain_squares(S,C,N,[FSquare|Rest]) :-
    X is sqrt(N),
    X1 is ceiling(X),
    C*X1 =< N,
    get_square(S,C,X1,0,Square),
    append(Square,FSquare),
    to_smtlib([
        all_different(FSquare)
    ]),
    C1 is C+1,
    constrain_squares(S,C1,N,Rest).

get_square(_,_,SN,SN,[]).
get_square([H|T],C,SN,Count,[Row|Rest]) :-
    C1 is C*SN-SN,
    cut_list(H,C1,NH),
    Count1 is Count+1,
    get_square_row(NH,SN,Row),
    get_square(T,C,SN,Count1,Rest).
get_square_row(_,0,[]).
get_square_row([H|T],C,[H|NT]) :-
    C1 is C-1,
    get_square_row(T,C1,NT).

cut_list(L,0,L).
cut_list([_|T],C,L) :-
    C > 0,
    C1 is C-1,
    cut_list(T,C1,L), !.





solve_sudoku_2(Rows, Rows) :- 
    set_prolog_flag(gc, off),
    z3_reset,
    %sudoku(Rows) , 
    append(Rows,Vars) , 
    to_smtlib(domain(Vars, 1, 9)), 
    transpose(Rows,Cols) , 
    to_smtlib([
        maplist(all_distinct,Rows) , 
        maplist(all_distinct,Cols)
     ]), 
    Rows = [R1,R2,R3,R4,R5,R6,R7,R8,R9] , 
    different_squares(R1,R2,R3) , different_squares(R4,R5,R6) , different_squares(R7,R8,R9) , 
    z3_labeling([ff],Vars) , 
    print_sudoku(Rows),
    z3_reset.

different_squares([],[],[]).       
different_squares([A,B,C|T1],[D,E,F|T2],[G,H,I|T3]) :-     
    to_smtlib(all_distinct([A,B,C,D,E,F,G,H,I])),      
    different_squares(T1,T2,T3).



sudoku([[_,3,_,_,_,_,_,_,_],
        [_,_,_,1,9,5,_,_,_],
        [_,_,8,_,_,_,_,6,_],
        [8,_,_,_,6,_,_,_,_],
        [4,_,_,8,_,_,_,_,1],
        [_,_,_,_,2,_,_,_,_],
        [_,6,_,_,_,_,2,8,_],
        [_,_,_,4,1,9,_,_,5],
        [_,_,_,_,_,_,_,7,_]]).



print_sudoku([]).
print_sudoku([H|T]) :- 
    write(H) , nl , 
    print_sudoku(T).



:- begin_tests(sudoku).

alldiff(L) :-
    all_different(L), !.
alldiff(L) :-
    print(not_all_different(L)), nl, fail.

correct_solution(L) :-
    ground(L),
    maplist(alldiff,L),
    transpose(L,TL),
    maplist(alldiff,TL).


test(unsolvable,[fail]) :-
    solve_sudoku([
    [1,2,3,4,5,6,7,8,_],
    [_,_,_,_,_,_,_,9,1],
    [_,_,_,_,_,_,_,_,2],
    [_,_,_,_,_,_,_,_,3],
    [_,_,_,_,_,_,_,_,4],
    [_,_,_,_,_,_,_,_,5],
    [_,_,_,_,_,_,_,_,6],
    [_,_,_,_,_,_,_,_,7],
    [_,_,_,_,_,_,_,_,8]],_), z3_reset.

test(unsolvable2,[fail]) :-
    solve_sudoku([
    [1,2,3,4,5,6,_,_,_],
    [_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,7,_,_],
    [_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,7,_],
    [_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,7]],_), z3_reset.

test(wikipedia,[nondet]) :-
    solve_sudoku([
    [_,3,_,_,_,_,_,_,_],
    [_,_,_,1,9,5,_,_,_],
    [_,_,8,_,_,_,_,6,_],
    [8,_,_,_,6,_,_,_,_],
    [4,_,_,8,_,_,_,_,1],
    [_,_,_,_,2,_,_,_,_],
    [_,6,_,_,_,_,2,8,_],
    [_,_,_,4,1,9,_,_,5],
    [_,_,_,_,_,_,_,7,_]],
    Sol), !,
    Sol ==
    [[5, 3, 4, 6, 7, 8, 9, 1, 2],
     [6, 7, 2, 1, 9, 5, 3, 4, 8],
     [1, 9, 8, 3, 4, 2, 5, 6, 7],
     [8, 5, 9, 7, 6, 1, 4, 2, 3],
     [4, 2, 6, 8, 5, 3, 7, 9, 1],
     [7, 1, 3, 9, 2, 4, 8, 5, 6],
     [9, 6, 1, 5, 3, 7, 2, 8, 4],
     [2, 8, 7, 4, 1, 9, 6, 3, 5],
     [3, 4, 5, 2, 8, 6, 1, 7, 9]].

test(some_16,[nondet]) :-
    solve_sudoku([
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,1,_,9,5,_,_,_,_,_,_,_,_],
    [_,_,8,_,_,_,_,_,_,_,6,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [8,_,_,_,_,6,_,_,_,_,_,_,_,_,_,_],
    [_,4,_,_,8,_,_,_,_,_,_,1,_,_,_,_],
    [_,_,_,_,_,_,2,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,6,_,_,_,_,_,_,2,8,_,_,_,_,_],
    [_,_,_,_,4,_,1,9,_,_,_,5,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,7,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_]],L), !,
    length(L,16),
    correct_solution(L).

test(empty_16,[nondet]) :-
    solve_sudoku([
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_]],L), !,
    L = [
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],
    [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_]],
    correct_solution(L).

test(worlds_hardest,[nondet]) :-
    solve_sudoku([
    [8,_,_,_,_,_,_,_,_],
    [_,_,3,6,_,_,_,_,_],
    [_,7,_,_,9,_,2,_,_],
    [_,5,_,_,_,7,_,_,_],
    [_,_,_,_,4,5,7,_,_],
    [_,_,_,1,_,_,_,3,_],
    [_,_,1,_,_,_,_,6,8],
    [_,_,8,5,_,_,_,1,_],
    [_,9,_,_,_,_,4,_,_]],L), !,
    length(L,9),
    correct_solution(L).

test(large_hole,[nondet]) :-
    solve_sudoku([
    [_,_,6,7,_,3,5,_,_],
    [_,_,_,_,4,_,_,_,_],
    [5,_,_,_,_,_,_,_,2],
    [9,_,_,_,_,_,_,_,7],
    [_,3,_,_,_,_,_,4,_],
    [8,_,_,_,_,_,_,_,1],
    [1,_,_,_,_,_,_,_,4],
    [_,_,_,_,_,_,_,_,_],
    [_,5,9,2,6,7,3,1,_]],L), !,
    length(L,9),
    correct_solution(L).

:- end_tests(sudoku).
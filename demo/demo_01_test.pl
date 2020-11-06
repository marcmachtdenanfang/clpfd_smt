%:- use_module(library(clpfd)).
:- use_module('../src/clpfd_smt_interface').
:- use_module(library(lists)).

sudoku([[_,3,_,_,_,_,_,_,_],
        [_,_,_,1,9,5,_,_,_],
        [_,_,8,_,_,_,_,6,_],
        [8,_,_,_,6,_,_,_,_],
        [4,_,_,8,_,_,_,_,1],
        [_,_,_,_,2,_,_,_,_],
        [_,6,_,_,_,_,2,8,_],
        [_,_,_,4,1,9,_,_,5],
        [_,_,_,_,_,_,_,7,_]]).

main :-
    z3_init,
    sudoku(Rows), 
    append(Rows,Vars),
    to_smtlib(domain(Vars, 1, 9)), 
    transpose(Rows,Cols), 
    to_smtlib([
	maplist(all_distinct,Cols), 
	maplist(all_distinct,Rows)]), 
    Rows = [R1,R2,R3,R4,R5,R6,R7,R8,R9], 
    different_squares(R1,R2,R3), 
    different_squares(R4,R5,R6), 
    different_squares(R7,R8,R9),
    z3_labeling([ff], Vars),
    print_sudoku(Rows).

different_squares([],[],[]).       
different_squares([A,B,C|T1],[D,E,F|T2],[G,H,I|T3]) :-     
  to_smtlib(all_distinct([A,B,C,D,E,F,G,H,I])),
  different_squares(T1,T2,T3).

print_sudoku([]).
print_sudoku([H|T]) :- 
    write(H), nl, 
    print_sudoku(T).

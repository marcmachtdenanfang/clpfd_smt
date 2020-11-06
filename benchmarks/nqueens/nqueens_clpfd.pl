/**********************************************************************************************
 * sample call:
 * ?- [nqueens_clpfd].
 * ?- nqueens(8, Rows).
 **********************************************************************************************/
:- use_module(library(clpfd)).

num_sols(N, Number_Of_Solutions) :-
    statistics(runtime, [T0|_]),

    findall(Sol, nqueens(N, Sol), Solutions),
    length(Solutions, Number_Of_Solutions),

    statistics(runtime, [T1|_]),
    format('N-queens took ~3d seconds', [T1-T0]).


nqueens(N,Rows) :-
    length(Rows,N),
    domain(Rows, 1, N), 
    all_different(Rows),
    no_attack(Rows),
    labeling([ff],Rows),
    true.


no_attack([]) :- !.
no_attack([Var|T]) :-
    no_attack_aux(Var,T,1),
    no_attack(T).
no_attack_aux(_,[],_).
no_attack_aux(Var,[Var2|T],N) :-
    Var #\= Var2 + N, 
    Var #\= Var2 - N,
    N1 is N + 1,    
    no_attack_aux(Var,T,N1).

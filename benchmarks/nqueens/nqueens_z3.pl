/**********************************************************************************************
 * example loop for our program. 
 * main(+N). 
 * N is an integer. 
 * 
 * sample call:
 * ?- [nqueens_z3].
* ?- main(8, Rows).
**********************************************************************************************/

:- module(nqueens_z3, [num_sols/2]).
:- use_module('../../src/clpfd_smt_interface').    % provides all predicates


num_sols(N, Number_Of_Solutions) :-
    set_prolog_flag(gc, off),
    %set_prolog_flag(gc_margin, 10000000),
    
    statistics(runtime, [T0|_]),

    findall(Sol, main(N, Sol), Solutions),
    length(Solutions, Number_Of_Solutions),
    
    statistics(runtime, [T1|_]),
    format('N-queens took ~3d seconds', [T1-T0]),

    z3_reset,
    set_prolog_flag(gc, on).


main(N, Rows) :-
    % call before running benchmark
    %set_prolog_flag(gc_margin, 1000000),
    set_prolog_flag(gc, off),

    z3_init,

    statistics(runtime, [T0|_]),
    nqueens(N, Rows),
    statistics(runtime, [T1|_]),
    format('runtime was ~3d seconds\n', [T1-T0]),
    z3_labeling([logic('QF_FD')], Rows),

    %write('Vars: '), write(Rows),nl,
    %write('Solution: '), write(Solution), nl,

    %findall((Row,Col), nth1(Col,Rows,Row), Pretty_Solution),
    
    %print_minutes(Runtime, Message),
    true.


nqueens(N,Rows) :-
    length(Rows,N),
    to_smtlib([
        domain(Rows, 1, N), 
        all_different(Rows)
    ]),
    no_attack(Rows).


no_attack([]) :- !.
no_attack([Var|T]) :-
    no_attack_aux(Var,T,1),
    no_attack(T).
no_attack_aux(_,[],_).
no_attack_aux(Var,[Var2|T],N) :-
    to_smtlib([
        Var #\= Var2 + N, 
        Var #\= Var2 - N
        ]),
    N1 is N + 1,    
    no_attack_aux(Var,T,N1).
    
    % "N1 is N+1" can also be asserted. Creates tons of extra constants though.
    % Also it breaks the system. Only up to N=62 can be solved. 
    % Afterwards something goes wrong, returning unsatisfiable.
    % nqueens(61, Rows) with "N1 is N+1" asserted takes 5 seconds, without takes 3.7 seconds.

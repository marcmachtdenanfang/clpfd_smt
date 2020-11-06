:- use_module('../../src/clpfd_smt_interface').    % provides all predicates

/**********************************************************************************************
 * example loop for our program. 
 * main(+N, +Filename). 
 * N is an integer. 
 * Filename is an atom. 
 * 
 * sample call:
 * ?- [nqueens_smt].
 * ?- main(8, 'nqueens.smt2').
 **********************************************************************************************/
main(N, Filename) :-
    nqueens(N, Rows),
    smtlib2_file([], Rows, Filename),
    smt_retractall(_Constraints, _Vars),
    %labeling([ffc],Rows),
    %findall((Row,Col), nth1(Col,Rows,Row), Solution),
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

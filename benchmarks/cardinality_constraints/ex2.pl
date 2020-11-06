:- use_module('../../clpfd_smt/clpfd_smt_interface.pl').

main([X,Y,Z]) :-
    z3_init,
    L = [X,Y,Z],
    Vars = L,
    to_smtlib([
            global_cardinality(L, [1-2,3-1]),
            B in 0..1
        ]),
    z3_labeling([logic('LIA')], Vars),
    /*write('Solution: '),write(Solution),nl,
    write('X: '), write(X), nl,
    write('Y: '), write(Y), nl,
    write('Z: '), write(Z), nl,
    z3_reset,*/
    true.

% IT WORKS:
% ?- z3_init, Vars = [X,Y,Z], to_smtlib([global_cardinality(Vars, [1-2,3-1])]), z3_labeling([logic('LIA')], Vars, Solution).
% Vars = [1,3,1] ? ;
% Vars = [3,1,1] ? ;
% Vars = [1,1,3] ? ;
% no

% vs CLPFD:
% ?- Vs = [_,_,_], global_cardinality(Vs, [1-2,3-_]), labeling([], Vs).
% Vs = [1,1,3] ? ;
% Vs = [1,3,1] ? ;
% Vs = [3,1,1] ? ;
% no

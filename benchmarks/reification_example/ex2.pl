:- use_module('../../src/clpfd_smt_interface.pl').

main :-
    z3_init,
    code([X,Y,Z,W,B,B1]),
    z3_labeling([logic('LIA')], [W,X,Y,Z,B,B1], Solution),
    write('Solution: '),write(Solution),nl,
    write('W: '), write(W), nl,
    write('X: '), write(X), nl,
    write('Y: '), write(Y), nl,
    write('Z: '), write(Z), nl,
    z3_reset.

code([X,Y,Z,W,B,B1]) :-
    to_smtlib([
            X #= Y #<=> B, 
            X #= 2, 
            Y #= 2, 
            Z #= 3+B, 
            Z #= 4 #<=>B1,
            W #= B1
            ]).
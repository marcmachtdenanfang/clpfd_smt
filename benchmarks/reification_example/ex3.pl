:- use_module('../../src/clpfd_smt_interface.pl').

main :-
    z3_init,
    Vars = [X,Y,Z,W,B,B1],
    code(Vars),
    z3_labeling([logic('LIA')], Vars),
    write('Solution: '),write(Vars),nl,
    write('W: '), write(W), nl,
    write('X: '), write(X), nl,
    write('Y: '), write(Y), nl,
    write('Z: '), write(Z), nl,
    %z3_reset,
    true.

code([X,Y,Z,W,B,B1]) :-
    to_smtlib([
        X #= Y #<=> B, 
        X #= 2, 
        Y #= 2, 
        Z #= 3+B, 
        % Compilation of reification is order agnostic.
        W #= B1,
        Z #= 4 #<=>B1
    ]).
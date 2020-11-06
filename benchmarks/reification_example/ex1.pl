:- use_module('../../src/clpfd_smt_interface.pl').

/*
Regarding QF_FD:
if 
*/

main :-
    z3_init,
    to_smtlib([
        %B in 0..1,
        all_distinct([X,Z]),
        X#<Z,
        X #= Y #<=> B, 
        X#=2#\/X#=5, 
        Y#=2,
        Z in 0..4,
        Z#=X+B,
        %sum([X,Z],#=,D) % does not work for qffd
        sum([X,Z],#=,5) % does work for qffd
    ]),
    % checking the possibilities of qffd
    z3_labeling([logic('QF_FD')], [X,Y,Z,B], Solution),
    write('Solution: '),write(Solution),nl,
    write('X: '), write(X), nl,
    write('Y: '), write(Y), nl,
    write('Z: '), write(Z), nl,
    z3_reset.

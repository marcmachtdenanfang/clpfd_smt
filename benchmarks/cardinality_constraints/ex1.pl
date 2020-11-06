:- use_module('../../src/clpfd_smt_interface.pl').

main([X,Y,Z]) :-
    z3_init,
    L = [X,Y,Z],
    Vars = L,
    to_smtlib([
            count(3,L,#<, 1),
            X in 1..5,
            Y in -1..2,
            Z in 2..10100101001010
        ]),
    z3_labeling([logic('LIA')], Vars),
    write('Solution: '),write(Vars),nl,
    write('X: '), write(X), nl,
    write('Y: '), write(Y), nl,
    write('Z: '), write(Z), nl,
    %z3_reset,
    true.


% CLPFD:
% ?- L = [X,Y,Z], X in 1..5, Y in -1..2, Z in 2..10100101001010, count(3,L,#<, 1).
% X in(1..2)\/(4..5),
% Y in-1..2,
% Z in{2}\/(4..10100101001010) ? ;
% no

% Z3 results can vary as it cannot return ranges.
% As long as X \= 3 and Z \= 3 everything is fine.
%
% Z3:
% ?- main.
% Solution: [4,0,4]
% X: 4
% Y: 0
% Z: 4
% yes




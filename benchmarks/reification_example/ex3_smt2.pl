:- use_module('../../src/clpfd_smt_interface.pl').

main :-
    code([X,Y,Z,W,B,B1]),
    smtlib2_file([logic('LIA')], [W,X,Y,Z,B,B1], 'ex3.smt2'),
    true.

code([X,Y,Z,W,B,B1]) :-
    to_smtlib([
            X #= Y #<=> B, 
            X #= 2, 
            Y #= 2, 
            Z #= 3+B, 
            % Compilation of reification is order agnostic.
            W #= B1,
            Z #= 4 #<=> B1
        ]).
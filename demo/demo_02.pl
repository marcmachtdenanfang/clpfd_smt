:- use_module('../src/clpfd_smt_interface.pl').

main :-
    z3_reset,
    Vars = [X,Y,Z,W,_B1,_B2],
    code(Vars),
    z3_labeling([logic('LIA')], Vars),
    write('Solution: '),write(Vars),nl,
    write('W: '), write(W), nl,
    write('X: '), write(X), nl,
    write('Y: '), write(Y), nl,
    write('Z: '), write(Z), nl,
    %z3_reset,
    true.

code([X,Y,Z,W,B1,B2]) :-
    to_smtlib([
        X #= Y #<=> B1, 
        X #= 2, 
        Y #= 2, 
        Z #= 3+B1, 
        % Compilation of reification is order agnostic.
        W #= B2,
        Z #= 4 #<=>B2
    ]).

main2 :-
    z3_reset,
    Vars = [X,Y,Z,W,_B1,_B2],
    code(Vars),
    smtlib2_file([logic('LIA')], Vars, 'demo_02.smt2'),
    write('Solution: '),write(Vars),nl,
    write('W: '), write(W), nl,
    write('X: '), write(X), nl,
    write('Y: '), write(Y), nl,
    write('Z: '), write(Z), nl,
    %z3_reset,
    true.
:- use_module('../src/clpfd_smt_interface').
:- use_module(library(clpfd)).

all_solutions(N) :-
    z3_init,

    statistics(runtime, [T0,_]),
    length(A,3), 
    length(B,3), 
    append(A,B,Vars), 
    to_smtlib([
        domain(Vars,1,3), 
        lex_chain([A,B])
    ]), 
    statistics(runtime, [T1,_]),

    statistics(runtime, [L0, _]),
    findall(X, z3_labeling([],Vars), L),
    statistics(runtime, [L1, _]),

    format('clpfd_smt runtime: ~3d\n', [T1-T0]),
    format('z3 labeling with backtracking: ~3d \n', [L1-L0]),
    length(L, N),
    z3_stop.

all_solutions_clpfd(N) :-
    statistics(runtime, [T0,_]),
    length(A,3), 
    length(B,3), 
    append(A,B,Vars), 
    domain(Vars,1,3), 
    lex_chain([A,B]),
    statistics(runtime, [T1,_]),

    statistics(runtime, [L0, _]),
    findall(X, labeling([ff],Vars), L),
    statistics(runtime, [L1, _]),

    format('clpfd runtime: ~3d\n', [T1-T0]),
    format('clpfd labeling with backtracking: ~3d \n', [L1-L0]),
    length(L, N).

    %findall(X, main_clpfd(A,B), L),
    %length(L, N).

main(A,B) :-
    z3_init,
    length(A,3), 
    length(B,3), 
    append(A,B,Vars), 
    to_smtlib([
        domain(Vars,1,3), 
        lex_chain([A,B])
    ]), 
    z3_labeling([],Vars).

main_clpfd(A,B) :-
    length(A,3), 
    length(B,3), 
    append(A,B,Vars), 
    domain(Vars,1,3),
    lex_chain([A,B]),
    labeling([ff], Vars).
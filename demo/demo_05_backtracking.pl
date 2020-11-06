:- use_module(library(clpfd)).
:- use_module('../src/clpfd_smt_interface').

main_clpfd(A) :-
    length(A,3), 
    X in 1..10,
    bool_channel(A,X,#=,1), 
    labeling([],A).

main1(A) :-
    z3_reset, 
    length(A,3), 
    to_smtlib([
        X in 1..10, 
        bool_channel(A,X,#=,1)
    ]), 
    z3_labeling([],A).

main2(Vars) :-
    z3_reset, 
    length(A,3), 
    to_smtlib([
        X in 1..10, 
        bool_channel(A,X,#=,1)
    ]), 
    append(A,[X],Vars),
    z3_labeling([],Vars).
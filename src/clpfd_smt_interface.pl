:- module(clpfd_smt_interface, [
        ins/2,              % clpfd_smt_base/smt_compiler
        to_smtlib/1,        % clpfd_smt_base
        get_all_constraints/1, 
        smt_constraint/2,   % clpfd_smt_base
        var/2,              % clpfd_smt_base
        var_bool/3,
        smt_retractall/2,   % clpfd_smt_base
        smtlib2_file/3,     % clpfd_smtlib2
        z3_labeling/2,
        z3_labeling/3,      % clpfd_z3
        z3_init/0,
        z3_reset/0,
        z3_stop/0
    ]).

:- use_module(library(file_systems)).

:- ensure_loaded(clpfd_smt_base).
:- ensure_loaded(clpfd_smtlib2).
:- if((file_exists('clpfd_z3.so') ; file_exists('clpfd_z3.bundle'))).
    :- ensure_loaded(clpfd_z3).
:- endif.

:- if(\+file_exists('clpfd_z3.so')).
:- initialization write('\nThe clpfd_z3.so library was not found.\nIt is not possible to interface to Z3.\nGenerating SMT-LIB2 code to file is still possible.\n\n').
:- endif.

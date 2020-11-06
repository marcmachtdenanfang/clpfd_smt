:- module(clpfd_smtlib2, [smtlib2_file/3]).

:- use_module(clpfd_smt_base).
:- use_module(library(codesio)).
:- use_module(printer_ext).

/**********************************************************************************************
 * This API provides ways to translate to smtlib2, for compatibility with 
 * solvers other than Z3.
 * 
 * smtlib2_to_file(+Options, +Vars, +Filename) creates a parseable .smt2 file.
 * 
 * Options can be an empty list. 
 * Vars are the variables, that need labeling 
 *   -> does not make too much sense, because we merely generate a file the user can send to the solver of their liking
 * Filename should be filename.smt2
***********************************************************************************************/
smtlib2_file(Optionslist, Vars, Filename) :-
    findall(Var_Code, var(Var_Code, _Var_Atom), Var_Codes),
    smt_declare_vars(Var_Codes, "Int", Var_Declaration_String),

    findall((Bool_Codes, Int_Atom), var_bool(Bool_Codes, _Bool_Atom, Int_Atom), Bool_Vars),
    (Bool_Vars = []
        ->
            Bool_Declaration_String = "", Bool_to_Int_Assertions_String = ""
        ;
            get_bool_codes(Bool_Vars, Bool_Codes_List),
            smt_declare_vars(Bool_Codes_List, "Bool", Bool_Declaration_String),
            mk_bool_to_int_assertion(Bool_Vars, Bool_to_Int_Assertions_String)
        ),

    get_all_constraints(Constraints),
    smt_assert_constraints(Constraints, Constraint_Assertion_String),
    
    append(Var_Declaration_String, Bool_Declaration_String, Declaration_String),
    append(Bool_to_Int_Assertions_String, Constraint_Assertion_String, Assertion_String),

    handle_options(Optionslist, Options_String),
    smt_get_value_string(Vars, Get_Value_String),
    gen_smt2_file(Filename, Declaration_String, Assertion_String, Options_String, Get_Value_String),
    smt_retractall(_,_).


/**********************************************************************************************
 * Generate smt2 file
***********************************************************************************************/
gen_smt2_file(Filename, Var_Declaration_String, Constraint_Assertion_String, Options_String, Get_Value_String) :-
    open(Filename, write, Out),
    write_string_to_stream(Out, "(set-logic LIA)"),
    newline(Out),
    write_string_to_stream(Out, Var_Declaration_String),          % var declarations have their own newline code.
    write_string_to_stream(Out, Constraint_Assertion_String),     % debug_assert(Filename, Out, 1, Constraint_Assertion_String), % flushes the stream after every character.
    % writes(Constraint_Assertion_String),                        % debugging only
    newline(Out),
    (Options_String = ""
        -> 
            true 
        ; 
            write_string_to_stream(Out, Options_String), 
            newline(Out)
    ),
    write_string_to_stream(Out, "(check-sat)"),
    newline(Out),
    write_string_to_stream(Out, Get_Value_String),
    newline(Out),
    write_string_to_stream(Out, "(get-info :all-statistics)"),
    newline(Out),
    close(Out).


/**********************************************************************************************
 * Option handling might deserve its own module.
***********************************************************************************************/
handle_options(_, "") :- !.


/**********************************************************************************************
 * in lieu of not finding the predicate to flush the streambuffer.
***********************************************************************************************/
debug_assert(Filename, Out, 0, String) :-
    close(Out), open(Filename, append, Out2), debug_assert(Filename, Out2, 1, String).
debug_assert(Filename, Out, Number, [Code|Tail]) :-
    put_code(Out, Code),
    N is Number - 1,
    debug_assert(Filename, Out, N, Tail).


/**********************************************************************************************
 * Generate a (get-value (V1 ... Vn)) string.
***********************************************************************************************/
smt_get_value_string(Vars, String) :-
    smt_get_value_string_aux(Vars, "))", Temp_String),
    append("(get-value (", Temp_String, String).
smt_get_value_string_aux([], String, String) :- !.
smt_get_value_string_aux([Var|Tail], Accumulator, String) :-
    write_to_codes(Var, Codes),
    append(Codes, " ", Codes_with_blank),
    append(Codes_with_blank, Accumulator, Temp),
    smt_get_value_string_aux(Tail, Temp, String).


/**********************************************************************************************
 * Handling boolean Variables
 * i.e.:
 *   for each reification variable (boolean) Xi generate a constraint that
 *   returns the integer equivalent.
 *  (assert 
        (and 
            (= (ite X1$bool 1 0) X1)
            ...
            (= (ite XN$bool 1 0) XN)
        )
    )
***********************************************************************************************/
get_bool_codes([], []) :- !.
get_bool_codes([(Bool_Codes, _)|Tail], [Bool_Codes|Result]) :-
    get_bool_codes(Tail, Result).

mk_bool_to_int_assertion(Bool_Vars, Result) :-
    mk_bool_to_int_assertion_aux(Bool_Vars, "", T0),
    append("(assert (and ", T0, T1),
    append(T1, "))\n", Result).
mk_bool_to_int_assertion_aux([], Result, Result) :- !.
mk_bool_to_int_assertion_aux([(Bool_Codes, Int_Atom)|Tail], Acc, Result) :-
    append("(= ", "(ite ", T0),
    append(T0, Bool_Codes, T1),
    append(T1, " 1 0) ", T2),
    atom_codes(Int_Atom, Int_Codes),
    append(T2, Int_Codes, T3),
    append(T3, ") ", T4),
    append(T4, Acc, New_Acc),
    mk_bool_to_int_assertion_aux(Tail, New_Acc, Result).
    


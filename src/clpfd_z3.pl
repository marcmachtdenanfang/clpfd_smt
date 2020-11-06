:- module(clpfd_z3, [z3_labeling/2,
                     %z3_labeling/3,
                     z3_init/0, 
                     z3_reset/0,
                     z3_stop/0, 
                     parser_example/0,
                     find_model_example2/0]).

:- use_module(library(lists)).
:- use_module(library(codesio)).
:- use_module(clpfd_smt_base).
%:- use_module('./timer/timer').
:- use_module(printer_ext).

foreign(init,                  c, init).
foreign(delete_context,        c, delete_context).
foreign(delete_solver,         c, delete_solver).
foreign(parse_assertion,       c, parse_assertion(+string)).
foreign(check_sat,             c, check_sat([-atom])).
foreign(parser_example,        c, parser_example).
foreign(find_model_example2,   c, find_model_example2).
foreign(declare_int,           c, declare_int(+string)).
foreign(declare_bool,          c, declare_bool(+string, +string)).
foreign(init_auxiliary_arrays, c, init_auxiliary_arrays(+integer)).
foreign(mk_solver_for_logic,   c, mk_solver_for_logic(+string)).
foreign(mk_solver_from_tactic, c, mk_solver_from_tactic(+string)).
foreign(init_solver_model,     c, init_solver_model).
foreign(dec_solver_model,      c, dec_solver_model).
foreign(get_value,             c, get_value(+string, [-integer])).


foreign_resource('clpfd_z3', [init, 
                              delete_context, 
                              parser_example,
                              find_model_example2,
                              parse_assertion,
                              declare_int,
                              declare_bool,
                              check_sat,
                              init_auxiliary_arrays,
                              mk_solver_for_logic,
                              mk_solver_from_tactic,
                              delete_solver,
                              init_solver_model,
                              dec_solver_model,
                              get_value
                              ]).

:- load_foreign_resource(clpfd_z3).


:- dynamic solution/1.              %% [('VAR'(Atom), Value) | Tuple_Tail],
:- dynamic z3_is_running/0.
:- dynamic solver_is_initialized/0.    
:- dynamic backtracking_succeded/0.


/**********************************************************************************************
 * Recommended way to initialize Z3 solver.
 * Removes all previous side effects from using clpfd_smt_interface predicates.
 * IMPORTANT: call before using to_smtlib!
***********************************************************************************************/
z3_reset :- 
    z3_is_running,
    solver_is_initialized,
    !,
    delete_solver,
    delete_context, 
    retract(z3_is_running),
    retract(solver_is_initialized),
    smt_retractall(_,_),
    retractall(solution(_)),
    z3_init.
z3_reset :-
    z3_is_running,
    !,
    delete_context,
    retract(z3_is_running),
    smt_retractall(_, _),
    retractall(solution(_)),
    z3_init.
z3_reset :-
    smt_retractall(_, _),
    retractall(solution(_)),
    z3_init.


/**********************************************************************************************
 * This or z3_reset is necessary to initialize Z3 solver.
 * Otherwise z3_labeling yields segfault error.
 * 
 * One can use z3_reset instead of z3_init, z3_labeling has already been called.
***********************************************************************************************/
z3_init :- z3_is_running, !, z3_reset.
z3_init :- 
    init, 
    assert(z3_is_running), !.
z3_init :- 
    write("There MIGHT be an error with your clpfd_z3.so shared library.\n").


/**********************************************************************************************
 * z3_stop/0 removes all side effects that occur by using clpfd_smt_interface predicates.
***********************************************************************************************/
z3_stop :- 
    z3_is_running,
    solver_is_initialized,
    !,
    delete_solver,
    delete_context, 
    retract(z3_is_running),
    retract(solver_is_initialized),
    smt_retractall(_,_),
    retractall(solution(_)).
z3_stop :- 
    z3_is_running, 
    !,
    delete_context,
    retract(z3_is_running),
    smt_retractall(_,_),
    retractall(solution(_)),
    retractall(solver_is_initialized).
z3_stop.




/**********************************************************************************************
 * z3_labeling(+Options, +Vars).
 * Regarding Options:
 *  setting a logic: logic('LIA'). 
 *  logic('LIA') is equivalent to tactic('lia').
 *  If all Variables have finite bounds, you can use logic('QF_FD')/tactic('qffd').
 *
 *  There are more logics/tactics available. The above two seem to be best.
 *  QF_LIA seems to be almost always slower than LIA. 
 * 
 * More options (such as maximize/minimize) can be implemented in the future.
 *
 * Vars are the variables that should be labeled.
 *
 * z3_labeling consists of two phases:
 *  phase one: 
        Find a solution.
 *  phase two:
        Backtrack over all possible solutions, until no more solutions are found.
***********************************************************************************************/
z3_labeling(Options, Vars) :-
    z3_labeling(Options, Vars, _).
z3_labeling(Options, Vars, Solution) :-
    (
        z3_labeling_phase_one(Options, Vars, Solution) 
    ; 
        % Only backtrack if phase_one succeded which implies there is a solution.
        solution(_), 
        z3_labeling_phase_two(_, Vars, Solution)
    ).
z3_labeling_phase_two(_, Vars, Solution) :-
    % Only backtrack if there already exists a solution. So we check whether there is a solution.
    solution(_),
    (z3_backtracking(Vars, Solution) ; z3_labeling_phase_two(_, Vars, Solution)).
z3_backtracking(Vars, Solution) :-
    retract(solution(Solution_Var_Tuple)),
    backtracking_mk_constraints(Solution_Var_Tuple, Constraints),
    smt_assert_constraints(Constraints, Constraint_Assertion_String),
    %% Comment: Constraint_Assertion_String = "(assert (and (= _891 X) ... (= _N Y)))", where X and Y are Integers.
    append("(assert ", Temp1, Constraint_Assertion_String),
    append("(not ", Temp1, Temp2),
    append(Temp2, ")", Temp3), 
    append("(assert ", Temp3, Temp4),
    %% Comment: Temp4 = "(assert (not (and (= _891 X) ... (= _N Y))))"
    name(Constraints_eval, Temp4),
    parse_assertion(Constraints_eval),
    check_sat(Is_sat),
    (Is_sat 
        -> 
            init_solver_model,
            get_model_ungrounded(Vars, New_Solution_Var_Tuple, Solution), 
            Vars = Solution,
            assert(solution(New_Solution_Var_Tuple))
        ;
            write('There are no more solutions.\n'), 
            fail
    ).


backtracking_mk_constraints([], []).
backtracking_mk_constraints([(Var, Value)|Tail], [Constraint|Result]) :-
    backtracking_mk_constraints(Tail, Result),
    Constraint = '#='(Var, Value).


z3_labeling_phase_one(Options, Vars, Solution) :- 
    option_handler(Options, _Optimizing_Options), % creates the solver.
    statistics(runtime, [T0,_]),
    %timer_start(Compilation_Timer_1),
    findall(Var_Atom, var(_Var_Code, Var_Atom), Var_Atoms),
    length(Var_Atoms, Number_of_Int_Variables),
    findall((Bool_Atom, Bool_Int_Atom), var_bool(_, Bool_Atom, Bool_Int_Atom), Bool_Atoms),
    length(Bool_Atoms, Number_of_Bool_Variables),

    Number_of_Variables is Number_of_Int_Variables + Number_of_Bool_Variables,

    init_auxiliary_arrays(Number_of_Variables),
    declare_int_vars(Var_Atoms),
    declare_bool_vars(Bool_Atoms),

    %timer_end(Compilation_Timer_1),
    %total_runtime(Compilation_Timer_1, Runtime_1),

    %timer_start(Compilation_Timer_2),
    get_all_constraints(Constraints),
    smt_assert_constraints(Constraints, Constraint_Assertion_String),
    name(Constraints_eval, Constraint_Assertion_String),
    %timer_end(Compilation_Timer_2),
    %total_runtime(Compilation_Timer_2, Runtime_2),
    statistics(runtime, [T1,_]),
    
    %Runtime is Runtime_1 + Runtime_2,
    %format("Compilation took: ~3f seconds\n", [Runtime/1000]),
    format('Compilation CPU time ~3d seconds\n', [T1-T0]),
    parse_assertion(Constraints_eval),
    check_sat(Is_sat),
    Is_sat,

    init_solver_model,
    get_model_ungrounded(Vars, Solution_Var_Tuple, Solution), 
    Vars = Solution,
    assert(solution(Solution_Var_Tuple)),
    
    true.

/**********************************************************************************************
 * declare_int_vars, declare_bool_vars:
 *      they call functions from the foreign resource that declare variables using the Z3 C-API.
 * 
 * Declaring variables using SMT-LIB2 code yielded issues on backtracking.
***********************************************************************************************/
declare_int_vars([]).
declare_int_vars([Head|Tail]) :-
    declare_int(Head),
    declare_int_vars(Tail).

declare_bool_vars([]).
declare_bool_vars([(Bool_Atom, Int_Atom)|Tail]) :-
    declare_bool(Bool_Atom, Int_Atom),
    declare_bool_vars(Tail).


/**********************************************************************************************
 * get_model(+Vars, -Tuples, -Values)
 * Vars can contain 'VAR'('_some_adress') or Integers
 * Tuples contains 'VAR'-elements from "Vars" and their corresponding values. Used for backtracking, to assert their solution as an unwanted solution.
 * Values contains all Values either given by Z3 or by input list "Vars".
 *
 * Sometimes our input list "Vars" contains ground Integers.
 * Those integers will be ignored when retrieving solutions.
***********************************************************************************************/
% get_model([], [], []).
% get_model([X|Var_Tail], Tuple_Tail, [X|Value_Tail]) :-
%     integer(X),
%     get_model(Var_Tail, Tuple_Tail, Value_Tail).
% get_model(['VAR'(Head)|Var_Tail], [('VAR'(Head), Value)|Tuple_Tail], [Value|Value_Tail]) :-
%     get_value(Head, Value),
%     get_model(Var_Tail, Tuple_Tail, Value_Tail).


/**********************************************************************************************
 * get_model_ungrounded(+Vars, -Tuples, -Values)
 * Alternative get_model, when input list Vars has not been grounded with 'VARS'(Atom).
 *
 * Disable garbage collection. Otherwise this approach does not work reliably.
 *   => set_prolog_flag(gc, off).
***********************************************************************************************/
get_model_ungrounded([], [], []).
get_model_ungrounded([Head|Var_Tail], [('VAR'(Atom), Value)|Tuple_Tail], [Value|Value_Tail]) :-
    var(Head), !,
    write_to_codes(Head, Codes),
    name(Atom, Codes),
    get_value(Atom, Value),
    get_model_ungrounded(Var_Tail, Tuple_Tail, Value_Tail).
get_model_ungrounded([X|Var_Tail], Tuple_Tail, [X|Value_Tail]) :-
    integer(X),
    get_model_ungrounded(Var_Tail, Tuple_Tail, Value_Tail).


/**********************************************************************************************
 * option_handler(+Options, -Optimizers).
 * handles z3_labeling options.
 * currently on logic/1 and tactic/1 are handled.
 *
 * Optimizers might be supported in the future.
 *
 * If options did not specify a logic or a tactic, then default to LIA as logic. 
***********************************************************************************************/
option_handler([], []) :- 
    \+solver_is_initialized,
    mk_solver_for_logic('LIA'), !,
    assert(solver_is_initialized).
option_handler([], []) :- !.
option_handler([logic(Logic)|Tail], Optimizers) :-
    \+solver_is_initialized,
    mk_solver_for_logic(Logic), !,
    assert(solver_is_initialized),
    option_handler(Tail, Optimizers).
option_handler([tactic(Tactic)|Tail], Optimizers) :-
    \+solver_is_initialized,
    mk_solver_from_tactic(Tactic), !,
    assert(solver_is_initialized),
    option_handler(Tail, Optimizers).
option_handler([_|Tail], Optimizers) :-
    option_handler(Tail, Optimizers).




/*
https://rise4fun.com/Z3/tutorialcontent/optimization
Difference Logic
Z3 uses by default an implementation of dual Simplex to solve feasibility and primal Simplex for optimality. 
For arithmetical constraints that only have differences between variables, known as difference logic, 
Z3 furthermore contains alternative decision procedures tuned for this domain. These have to be configured explicitly. 
There is a choice between a solver tuned for sparse constraints (where the ratio of variables is high compared 
to number of inequalities) and a solver tuned for dense constraints.
load in editor

(set-option :smt.arith.solver 1) ; enables difference logic solver for sparse constraints
(set-option :smt.arith.solver 3) ; enables difference logic solver for dense constraints
(declare-const x Int)
(declare-const y Int)
(assert (>= 10 x))
(assert (>= x (+ y 7)))
(maximize (+ x y))
(check-sat)
(get-objectives)

*/


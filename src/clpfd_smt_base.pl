:- module(clpfd_smt_base,[
                            to_smtlib/1,
                            get_all_constraints/1,
                            smt_constraint/2, 
                            var/2, 
                            var_bool/3,
                            smt_assert_constraints/2, 
                            ins/2,
                            smt_retractall/2,
                            smt_declare_vars/3
                        ]).


:- use_module(smt_compiler).

:- use_module(library(clpfd)).
:- use_module(library(sets)).
:- use_module(library(lists)).
:- use_module(library(codesio)).

:- dynamic smt_constraint/2.    %% smt_constraint(Constraint, Grounded_VAR_List), 
                                %%  Grounded_VAR_List = ['VAR'('_891'),...]
                                %%  use: "term_variables(Constraint, Vars), Vars = Grounded_VAR_List." to retrieve identity of Vars.
:- dynamic var/2.               %% var(Var_Code, Var_Atom). => Var_Atom = 'VAR'('_891')
:- dynamic var_bool/3.          %% var_bool(Bool_Code, Bool_Atom, Var_Atom). => 


/**********************************************************************************************
 * smt_assert_constraints(+Constraints, -Constraint_Assertion_String)
 * returns a string with "(assert (and C1 C2 ... Cn))" for n > 1. 
 * else: (assert C1) 
 * Constraints have their own leading and trailing brackets.
***********************************************************************************************/
smt_assert_constraints(Constraints, Constraint_Assertion_String) :-
    smt_compile_constraints(Constraints, Constraint_Assertion_String).


/**********************************************************************************************
 * to_smtlib/1, asserts constraints that are given as its parameter. 
 * We store the named Grounded_VAR_List as well. Once we retract the constraints, 
 * term_variables are out of scope and will not unify with original Constraintvars. 
 * Solves the problem of "non-list" solutions (Such as Sudoku: solution is a matrix). 
 * => Unfortunately, it does NOT work reliably, with garbage collection on. 
 * Turn off garbage collection for it to work reliably!
***********************************************************************************************/

% Base case.
to_smtlib([]) :- !.


/**********************************************************************************************
 * handles:
 *      lex_chain/1
 * uses OR encoding described in:
 * "Encoding the lexicographic Ordering constraint in SAT Modulo Theories"
 * Hani A. Elgabou and Alan M. Frisch
***********************************************************************************************/
to_smtlib([lex_chain(Lists)|Tail]) :-
    !,
    
    to_smtlib_lex_chain_aux(Lists, Terms),
    append(Terms, Constraints),

    % to_smtlib_lex_chain(A, B, Constraints),
    to_smtlib(Constraints),
    to_smtlib(Tail).

/**********************************************************************************************
 * handles: 
 *      count/4
 *
 * Encodes count/4 into primitive constraints.
 * Primitive constraints then go on to be handled by to_smtlib.
***********************************************************************************************/
to_smtlib([count(Val, List, RelOp, Count)|Tail]) :-
    to_smtlib_count(count(Val, List, RelOp, Count), Constraints),
    !,
    to_smtlib(Constraints),
    to_smtlib(Tail).


/**********************************************************************************************
 * handles: 
 *      global_cardinality/2
 *
 * Encodes global_cardinality/2 into primitive constraints.
 * Primitive constraints then go on to be handled by to_smtlib.
***********************************************************************************************/
to_smtlib([global_cardinality(Xs, Vals)|Tail]) :-
    to_smtlib_global_cardinality(Xs, Vals, Constraints),
    !,
    to_smtlib(Constraints),
    to_smtlib(Tail).


/**********************************************************************************************
* handles: global_cardinality/3
* When option cost/2 is encountered, throw an error and stop.
* Option cost/2 changes the semantics of the constraints.
* It is not yet supported by the compiler.
*
* Future work: implement option:
* cost(Cost,Matrix)
*
* Definition by SICStus Prolog 4.6.0 manual:
*    Overrides any consistency/1 option value. 
*    A cost is associated with the constraint 
*    and reflected into the domain variable Cost. 
*    Matrix should be a d*n matrix of integers, 
*    represented as a list of d lists, each of length n. 
*    Assume that each Xi [in Xs] equals K(pi) [in Vals=Ki-Vi]. 
*    The cost of the constraint is then Matrix[1,p1]+…+Matrix[d,pd].
***********************************************************************************************/
to_smtlib([global_cardinality(Xs, Vals, Options)|Tail]) :-
    (gc_cost_option(Options) 
        -> 
            write('global_cardinality/3 with option cost/2 is not currently supported.\n'),
            throw(unsupported_constraint(global_cardinality(Xs, Vals, Options)))
        ;
            true
    ),
    to_smtlib_global_cardinality(Xs, Vals, Constraints),
    !,
    to_smtlib(Constraints),
    to_smtlib(Tail).


/**********************************************************************************************
 * handles: 
 *      all_distinct/2, 
 *      all_different/2, 
 *          where second argument is L #= R
***********************************************************************************************/
to_smtlib([Term|Tail]) :-
    nonvar(Term),
    (functor(Term, all_distinct, 2) ; functor(Term, all_different, 2)),
    !,
    Term =.. [Predicate, List, Options],
    handle_distinct_Options(Options, Option_Constraint),
    (Option_Constraint = [] -> true ; to_smtlib(Option_Constraint)),
    New_Term =.. [Predicate, List],
    to_smtlib(New_Term),
    to_smtlib(Tail).


/**********************************************************************************************
 * handles: 
 *      maplist/[2,3,4,5]
 *
 * Maplist is deconstructed such that it returns all constraints given their arguments.
 * Those deconstructed constraints are handled by to_smtlib.
***********************************************************************************************/
to_smtlib([Term|Tail]) :-               
    nonvar(Term),
    functor(Term, maplist, _Arity), 
    !,
    Term =.. [maplist, Predicate | Maplist_Args],
    to_smtlib_maplist(Predicate, Maplist_Args, Mapped_Predicates),
    append(Mapped_Predicates, Tail, Constraints),!,
    to_smtlib(Constraints).


/**********************************************************************************************
 * handles: 
 *      bool_and/2, 
 *      bool_or/2, 
 *      bool_xor/2 
 *
 * A compound term bool_constraint(Lits, Propositional_Operator) is created. 
 * Our compiler compiles the compound term bool_constraint with ease, due to LISP-like Syntax of SMT-LIB2.
 * 
 * We need to do it this way, so that Lit is registered as a reified boolean variable.
 * Test:
 * ?- to_smtlib(bool_xor([X,Y,Z],Lit)), 
      clpfd_smt_base:smt_constraint(Constraint, Vars), 
      term_variables(Constraint, Constraint_Vars), 
      Constraint_Vars = Vars, 
      smt_compiler:con2smt(Constraint,SMT), 
      atom_codes(A, SMT), 
      write(A).
 * A = '(= (xor  (= _843 1) (= _883 1) (= _923 1)) _981$bool)' ? ;
 * no
***********************************************************************************************/
to_smtlib([bool_and(Lits, Lit)|Tail]) :-
    !,
    to_smtlib([  (bool_constraint(Lits, #/\) #<=> Lit)  ]),
    to_smtlib(Tail).
to_smtlib([bool_or(Lits, Lit)|Tail]) :-
    !,
    to_smtlib([  (bool_constraint(Lits, #\/) #<=> Lit)  ]),
    to_smtlib(Tail).
to_smtlib([bool_xor(Lits, Lit)|Tail]) :-
    !,
    to_smtlib([  (bool_constraint(Lits, xor) #<=> Lit)  ]),
    to_smtlib(Tail).


/**********************************************************************************************
 * handles: 
 *      bool_channel/4
 *
 * Encodes bool_channel into primitive constraints.
 * Primitive constraints then go on to be handled by to_smtlib.
***********************************************************************************************/
to_smtlib([bool_channel(Lits, Y, RelOp, Offset)|Tail]) :-
    !,
    to_smtlib_bool_channel(Lits, Y, RelOp, Offset, Constraints),
    to_smtlib(Constraints),
    to_smtlib(Tail).


/**********************************************************************************************
 * handles: 
        reified Constraints
 *
 * Guard: checks whether constraint using #<=> is a reified constraint (might be propositional constraint)
 *
 * Names term variables, asserts unasserted term variables.
 *
 * Creates boolean variant for reification variable, and replaces reification variable in constraint
 * variable list with boolean variant.
 *
 * Asserts the boolean variant (if it has not been asserted yet).
 *
 * Finally asserts the constraint, given the altered constraint variable list.
***********************************************************************************************/
to_smtlib([(L #<=> R)|Tail]) :-
    is_reified_constraint((L #<=> R), Reified_Var), !,
    to_smtlib((Reified_Var in 0..1)),       % necessary, to make certain constraints qffd capable, such as global cardinality. => consult benchmark magicseq
    Head = (L #<=> R),
    term_variables(Head, Vars),
    name_variables(Vars, Grounded_VAR_List, Unasserted_Vars),
    make_bool_atom_and_codes(Reified_Var, Bool_Codes, Bool_Atom),
    write_to_codes(Reified_Var, Var_Codes),
    name(Var_Atom, Var_Codes),     % Var_Atom is the identifier of boolean's integer version
    (var_bool(_, Bool_Atom, _)     % Has this boolean been asserted before?
        -> true 
        ; assert(var_bool(Bool_Codes, Bool_Atom, Var_Atom))
    ),
    select('VAR'(Var_Atom), Grounded_VAR_List, 'VAR'(Bool_Atom), Adapted_VAR_List),
    % read as: select 'VAR'(Var_Atom) in Grounded_VAR_List and replace it with 'VAR'(Bool_Atom) in Adapted_VAR_List.
    assert_vars(Unasserted_Vars),
    asserta(smt_constraint(Head, Adapted_VAR_List)),
    to_smtlib(Tail).


/**********************************************************************************************
 * handles:
        primitive arithmetic constraints, 
        domain/3, 
        all_distinct/1, 
        all_different/1, 
        scalar_product/4,5, 
        sum/3
***********************************************************************************************/
to_smtlib([Head|Tail]) :-
    !,
    term_variables(Head, Vars),
    name_variables(Vars, Grounded_VAR_List, Unasserted_Vars),
    assert_vars(Unasserted_Vars),
    asserta(smt_constraint(Head, Grounded_VAR_List)),
    to_smtlib(Tail).
to_smtlib(X) :-
    to_smtlib([X]).


/**********************************************************************************************
 * assert_vars(+Vars)
 * Vars is a list of atoms that represent memory addresses of variables.
 * Such as: Vars = ['_891', '_895']
 *
 * Asserts standard (i.e. non-boolean) variables to the database.
***********************************************************************************************/
assert_vars([]) :- !.
assert_vars([Var_Atom|T]) :-
    name(Var_Atom, Codes),
    asserta(var(Codes, Var_Atom)),
    assert_vars(T).



/**********************************************************************************************
 * gc_cost_option(+Options).
 * Options is a list of legal global_cardinality options.
 *
 * True if Options contains cost/2.
***********************************************************************************************/
gc_cost_option([cost(_,_)|_]) :-
    true.
gc_cost_option([_|Tail]) :-
    gc_cost_option(Tail).


/**********************************************************************************************
 * used by to_smtlib/1 for reification variables:
 * 
 * Assuming adress of Var is _891
 *
 * ?- make_bool_atom_and_codes(Var, Bool_Codes, Bool_Atom).
 * Bool_Codes = [95,56,57,49,36,98,111,111,108],
 * Bool_Atom = '_891$bool' ? ;
 * no
***********************************************************************************************/
make_bool_atom_and_codes(Var, Bool_Codes, Bool_Atom) :-
    write_to_codes(Var, Var_Codes),
    append(Var_Codes, "$bool", Bool_Codes),
    atom_codes(Bool_Atom, Bool_Codes).


/**********************************************************************************************
 * leq = less-equal-than
***********************************************************************************************/
to_smtlib_lex_chain_aux([_], []) :- !.
to_smtlib_lex_chain_aux([A, B|Tail], [Terms|Constraints]) :-
    to_smtlib_lex_chain(A, B, Terms),
    to_smtlib_lex_chain_aux([B|Tail], Constraints).

to_smtlib_lex_chain(A, B, Constraints) :-
    !,
    make_reified_equality_constraints(A, B, [], Reified_Equality_Constraints, [], Reified_Equality_Vars),
    make_reified_less_than_constraints(A, B, [], Reified_Less_Than_Constraints, [], Reified_Less_Than_Vars),
    make_T3_Reif_Vars(Reified_Equality_Vars, Reified_Less_Than_Vars, Other_Constraints),
    append(Reified_Equality_Constraints, Reified_Less_Than_Constraints, Temp),
    append(Temp, Other_Constraints, Constraints).

make_reified_equality_constraints([], [], Constraint_Acc, Constraint_Acc, Vars_Acc, Reversed_Vars) :-
    reverse(Vars_Acc, Reversed_Vars), !.
make_reified_equality_constraints([A|A_Tail], [B|B_Tail], Constraint_Acc, Constraints, Vars_Acc, Vars) :-
    Term = (A = B #<=> Reification_Variable),
    make_reified_equality_constraints(A_Tail, B_Tail, [Term|Constraint_Acc], Constraints, [Reification_Variable|Vars_Acc], Vars).

make_reified_less_than_constraints([], [], Constraint_Acc, Constraint_Acc, Vars_Acc, Reversed_Vars) :-
    reverse(Vars_Acc, Reversed_Vars), !.
make_reified_less_than_constraints([A|A_Tail], [B|B_Tail], Constraint_Acc, Constraints, Vars_Acc, Vars) :-
    Term = (A < B #<=> Reification_Variable),
    make_reified_less_than_constraints(A_Tail, B_Tail, [Term|Constraint_Acc], Constraints, [Reification_Variable|Vars_Acc], Vars).

% Initially N is 1, then 2, then ..., then Final_N
% Once the value of N is Final_N, terminate.
make_T3_Reif_Vars(Reified_Equality_Vars, Reified_Less_Than_Vars, Constraints) :-
    do_smth(Reified_Equality_Vars, Reified_Less_Than_Vars, 1, Constraint_1, T3_Vars),       % T3_Vars includes T3_i for 1<=i<=n-1
    Constraint_2 = [bool_constraint(Reified_Equality_Vars, #/\) #<=> T3_n],
    %Constraint_3_1 = bool_constraint(T3_Vars, #\/),
    Reified_Less_Than_Vars = [Lt_1|_],
    %Constraint_3 = [bool_constraint([Constraint_3_1, Lt_1, T3_n], #\/)],
    append(T3_Vars, [Lt_1], Temp_1),
    append(Temp_1, [T3_n], Constraint_3_Vars),
    Constraint_3 = [bool_constraint(Constraint_3_Vars, #\/)],
    append(Constraint_1, Constraint_2, Temp_2),
    append(Temp_2, Constraint_3, Constraints).
    
do_smth(_, [_Lt_n], _, [], []) :- !.
do_smth(Eq_Vars, [_, Lt_Var|Lt_Tail], N, [Term|Constraints], [T3_i|T3_Vars]) :-
    inner_loop(Eq_Vars, Lt_Var, N, Conjunctions),
    Term = (bool_constraint(Conjunctions, #/\) #<=> T3_i),
    NN is N+1,
    do_smth(Eq_Vars, [_|Lt_Tail], NN, Constraints, T3_Vars).

%inner_loop([Eq_Var|_], Lt_Var, 1, [Term]) :- 
    %Term = (Eq_Var#=1 #/\ Lt_Var#=1), !.
inner_loop([Eq_Var|_], Lt_Var, 1, [Eq_Var, Lt_Var]) :- !.
inner_loop([Eq_Var|Tail], Lt_Var, N, [Eq_Var, Lt_Var|Constraints]) :-
    %Term = (Eq_Var#=1 #/\ Lt_Var#=1),
    NN is N-1,
    inner_loop(Tail, Lt_Var, NN, Constraints).

/**********************************************************************************************
 * https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus.html/Arithmetic_002dLogical-Constraints.html
 * 
 * bool_channel(+Lits, ?Y, +Relop, +Offset)   since release 4.3
 * 
 *     where Lits is a list of literals [L0,...,Lj], 
 *     Y is a domain variable, 
 *     RelOp is an arithmetic comparison as in Syntax of Arithmetic Expressions, 
 *     and Offset is an integer. 
 *     
 *     Expresses the constraint Li #<=> (Y RelOp i+Offset) for i in 0..j. 
 * 
 * ?- length(L,4), to_smtlib_bool_channel(L,3,#=,1,C).
 * L = [_A,_B,_C,_D],
 * C = [_A#<=>3#=0+1,_B#<=>3#=1+1,_C#<=>3#=2+1,_D#<=>3#=3+1] ? ;
 * no
***********************************************************************************************/
to_smtlib_bool_channel(Lits, Y, RelOp, Offset, Constraints) :-
    (   foreach(Constraint, Constraints),
        foreach(Lit, Lits), 
        count(I, 0, _N),
        param([Y, RelOp, Offset])
    do  T1 =.. [+, I, Offset],
        T2 =.. [RelOp, Y, T1],
        (var(Lit) -> Li = Lit
            ; Lit = 1 -> Li = true 
                ; Li = false
        ),
        Constraint =.. [#<=>, Li, T2]
    ).


/**********************************************************************************************
https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus.html/Arithmetic_002dLogical-Constraints.html

all_different(+Variables)
all_different(+Variables, +Options)
all_distinct(+Variables)
all_distinct(+Variables, +Options)

    where Variables is a list of domain variables. Each variable is constrained to take a value 
    that is unique among the variables. Declaratively, this is equivalent to an inequality constraint 
    for each pair of variables.

    Corresponds to all_different in MiniZinc.

    Options is a list of zero or more of the following:

    L #= R   since release 4.3

        where R should be an integer, and L an expressions of one of the following forms, where X1, …, Xj occur among Variables:

        X1 + ... + Xj
        X1*X1 + ... + Xj*Xj
        X1 * ... * Xj

        The given equation is a side constraint for the constraint to hold. A special bounds-consistency algorithm is used, 
        which considers the main constraint and the side constraints globally. This option is only valid 
        if the domains of X1, …, Xj consist of integers strictly greater than zero.
***********************************************************************************************/
handle_distinct_Options([], []) :- !.
handle_distinct_Options([(L #= R)|Tail], [(L #= R)|Result]) :-
    !, handle_distinct_Options(Tail, Result).
handle_distinct_Options([_|Tail], Result) :-
    handle_distinct_Options(Tail, Result).



/**********************************************************************************************
 * https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus.html/Arithmetic_002dLogical-Constraints.html
 * global_cardinality(+Xs,+Vals)
 * global_cardinality(+Xs,+Vals,+Options)
 * 
 *     where Xs = [X1,…,Xd] is a list of domain variables, and Vals = [K1-V1,…,Kn-Vn] is a list of pairs 
 *     where each key Ki is a unique integer and Vi is a domain variable. True if every element of Xs is 
 *     equal to some key and for each pair Ki-Vi, exactly Vi elements of Xs are equal to Ki.
 * 
 *     If either Xs or Vals is ground, and in many other special cases, then global_cardinality/[2,3]
 *     maintains domain consistency, but generally, bounds consistency cannot be guaranteed.
 *     A domain-consistency algorithm [Regin 96] is used, roughly linear in the total size of the domains. 
 * 
 * integer(Ki), 
 * Vi is domain variable.
 * assuming => global_cardinality([X1, X2], [K1-V1, K2-V2])
 * every X is equal to any K. => X1#=K1 #<=>BK11, X1#=K2 #<=>BK21, X1#=K3 #<=>BK31, X2#=K1 #<=>BK12, X2#=K2 #<=>BK22, X2#=K3#<=>BK32
 *   => because we use reified booleans, we do not need disjunctions!
 * exactly Vi elements of Xs are equal to Ki => sum([BK11, BK12], #=, V1), sum([BK21, BK22], #=, V2), sum([BK31, BK32], #=, V3).
***********************************************************************************************/
to_smtlib_global_cardinality(Xs, Vals, Constraints) :-
    glob_cardinality_to_reified_constraint(Xs, Vals, Xs_Constraints, Xs_Booleans),
    append(Xs_Constraints, Temp),
    mk_sum_constraints(Vals, Xs_Booleans, Sum_Constraints),
    /*append(Xs_Booleans, Booleans),
    to_smtlib(domain(Booleans, 0, 1)),*/
    append(Temp, Sum_Constraints, Constraints).



/**********************************************************************************************
 * mk_sum_constraints(+Vals, +Booleans, Constraints).
 * Vals is a list of Key-Value pairs
 * Constraint is equal to the sum of reified variables from Booleans, that are related
 * to Ki in Keys, with Vi in Vals.
 *
 * ?- glob_cardinality_to_reified_constraint([X1,X2,X3], [1-_,2-_,1-_,3-_], Cs, Bs), 
 *     mk_sum_constraints([_-1,_-2,_-3,_-4], Bs, Sum_Constraints).
 * Cs = [[X1 #= 1#<=> _A,  X1 #= 2 #<=> _B,  X1 #= 1 #<=> _C,  X1 #= 3 #<=> _D],
 *       [X2 #= 1#<=> _E,  X2 #= 2 #<=> _F,  X2 #= 1 #<=> _G,  X2 #= 3 #<=> _H],
 *       [X3 #= 1#<=> _I,  X3 #= 2 #<=> _J,  X3 #= 1 #<=> _K,  X3 #= 3 #<=> _L]],
 * Bs = [[_A,_B,_C,_D],[_E,_F,_G,_H],[_I,_J,_K,_L]],
 * Sum_Constraints = [sum([_A,_E,_I],#=,1),sum([_B,_F,_J],#=,2),sum([_C,_G,_K],#=,3),sum([_D,_H,_L],#=,4)] ? ;
 * no
***********************************************************************************************/
mk_sum_constraints([], _, []) :- !.
mk_sum_constraints([_Ki-Vi|Vals], Xs_Booleans, [Sum_Constraint|Result]) :-
    get_first_booleans(Xs_Booleans, First_Booleans, Booleans_Tail),
    Sum_Constraint =.. [sum, First_Booleans, #=, Vi],
    mk_sum_constraints(Vals, Booleans_Tail, Result).



/**********************************************************************************************
 * get_first_booleans(?Xs_Booleans, ?First_Booleans, ?Booleans_Tails)
 * Xs_Booleans is a list of lists.
 * First_Booleans is a list.
 * Booleans_Tails is a list of lists.
 * 
 * True if First_Booleans contains the Head of each list in Xs_Booleans
 * and Booleans_Tails contains the Tail of each list in Xs_Booleans.
 *
 * ?- clpfd_smt_base:get_first_booleans([[A1,A2,A3], [B1,B2,B3]], First_Booleans, Boolean_Tails).
 * First_Booleans = [A1,B1],
 * Boolean_Tails = [[A2,A3],[B2,B3]] ? ;
 * no
***********************************************************************************************/
get_first_booleans([], [], []).
get_first_booleans([List|Tail], [Head|Bools], [Bool_Tail|Bools_Tails]) :-
    List = [Head|Bool_Tail],
    get_first_booleans(Tail, Bools, Bools_Tails).



/**********************************************************************************************
 * called by to_smtlib_global_cardinality/3
 * 
 * glob_cardinality_to_reified_constraint(+Xs, +Vals, -Constraints, -Booleans).
 * Xs is a list of (domain) variables.
 * Vals is a list of Key-Value pairs.
 * Constraints is defined to be that any X in Xs is equal to some K,
 * and these relationships are stored into a reified variable.
 * Booleans is a Matrix of those reified variables, where each list in Booleans contains
 * the reified variables for X in Xs.
 *
 *
 * ?- glob_cardinality_to_reified_constraint([X1,X2,X3], [1-_,2-_,1-_,3-_], Cs, Bs), 
 *     get_first_booleans(Bs, First_Booleans, Boolean_Tails).
 * Cs = [[X1 #= 1 #<=> _A,  X1 #= 2 #<=> _B,  X1 #= 1 #<=> _C,  X1 #= 3 #<=> _D],
 *       [X2 #= 1 #<=> _E,  X2 #= 2 #<=> _F,  X2 #= 1 #<=> _G,  X2 #= 3 #<=> _H],
 *       [X3 #= 1 #<=> _I,  X3 #= 2 #<=> _J,  X3 #= 1 #<=> _K,  X3 #= 3 #<=> _L]],
 * Bs = [[_A,_B,_C,_D],[_E,_F,_G,_H],[_I,_J,_K,_L]],
 * First_Booleans = [_A, _E, _I],
 * Boolean_Tails = [[_B,_C,_D],[_F,_G,_H],[_J,_K,_L]] ? ;
 * no
***********************************************************************************************/
glob_cardinality_to_reified_constraint([], _, [], []) :- !.
glob_cardinality_to_reified_constraint([X|Xs], Vals, [Constraints|C_Tail], [Booleans|B_Tail]) :-
    (   foreach((Ki-_Vi), Vals), 
        foreach(C, Constraints), 
        foreach(B, Booleans), 
        param(X)
    do  Temp =.. [#=, X, Ki], C =.. [#<=>, Temp, B]
    ),
    glob_cardinality_to_reified_constraint(Xs, Vals, C_Tail, B_Tail).



/**********************************************************************************************
 * https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus.html/Arithmetic_002dLogical-Constraints.html
 * Regarding count/4:
 * 
 * True if N is the number of elements of List that are equal to Val and N RelOp Count.
 * count(+Val,+List,+RelOp,?Count) 
 * L = [X,Y,Z], X #= Val#<=>B1, Y#=Val#<=>B2, Z#=Val#<=>B3, sum([B1,B2,B3],#=, N), N RelOp Count.
 * sum(+Xs, +RelOp, ?Value)
 *
 * L=[X1,X2,X3], X1 in 1..3, X2 in 2..4, X3 in 3..5, count(3,L,#>=,3).
***********************************************************************************************/
to_smtlib_count(count(Val, List, RelOp, Count), Constraints) :-
    (   foreach(X, List), 
        foreach(Constraint, Constraint_List), 
        foreach(B, Booleans), 
        param(Val) 
    do  Constraint = (X #= Val #<=> B)
    ),
    Sum =.. [sum, Booleans, #=, N],
    C   =.. [RelOp, N, Count],
    Constraints = [C, Sum|Constraint_List].



/**********************************************************************************************
 * Args is a matrix of up to five lists and their respective arguments.
 * take all the first elements in correct order from the matrix and stack
 * them onto the final function call.
 *
 * clpfd_smt_base:to_smtlib(maplist(all_distinct, [[X,Y,1,2,a], [a,s,d,f,g]])).
 * => clpfd_smt_base:smt_constraint(X,Y).
 * X = all_distinct(a,s,d,f,g),
 * Y = [] ? ;
 * X = all_distinct(_A,_B,1,2,a),
 * Y = ['VAR'('_905'),'VAR'('_945')] ? ;
 * no
***********************************************************************************************/
to_smtlib_maplist(_, [], []) :- !.
to_smtlib_maplist(Predicate, Args, [Mapped_Predicate|Result]) :-
    Predicate =.. L,                                    % foo(X,Y) =.. [foo,X,Y]
    get_all_first_elements(Args, First_Args, Tails),    % Args = [[[1,2,3],[a,b,c]]], First_Args=[[1,2,3]], Tails= [[[a,b,c]]]
    First_Args \= [],
    append(L, First_Args, Temp),                        % Temp = [foo,X,Y,[1,2,3]]
    Mapped_Predicate =.. Temp,                          % Mapped_predicate = foo(X,Y,[1,2,3])
    to_smtlib_maplist(Predicate, Tails, Result).
to_smtlib_maplist(_Predicate, _Args, _Result).

get_all_first_elements([[]], [], []) :- !.
get_all_first_elements([[E1|T1]],                            [E1],             [T1])          :- !.   % maplist/2
get_all_first_elements([[E1|T1], [E2|T2]],                   [E1, E2],         [T1,T2])       :- !.   % maplist/3
get_all_first_elements([[E1|T1], [E2|T2], [E3|T3]],          [E1, E2, E3],     [T1,T2,T3])    :- !.   % maplist/4
get_all_first_elements([[E1|T1], [E2|T2], [E3|T3], [E4|T4]], [E1, E2, E3, E4], [T1,T2,T3,T4]) :- !.   % maplist/5



/**********************************************************************************************
  is_reified_constraint(+Constraint, -Reification_Variable).
 * True if Constraint is a reified constraint.
 * Reified constraints are of the form 'Left #<=> Right', 
 * where either Left or Right is Reification_Variable.
***********************************************************************************************/
is_reified_constraint(Left #<=> _Right, Left) :-
    var(Left), !.
is_reified_constraint(_Left #<=> Right, Right) :-
    var(Right), !.



/**********************************************************************************************
 * Returns all Constraints that are in the smt_constraint/2 database. 
 * Variables in these constraints are:
 *  'VAR'(memoryadress). 
 * Memoryadress is the adress of the original variable. 
 * E.g. memoryadress = '_890'

 * This is the "ungrounded" approach.
 * It does not work reliably, when garbage collection is turned on, and the number of 
 * variable allocations surpasses gc_margin!
 * => set_prolog_flag(gc, off).
 * Or increase gc_margin
 * => set_prolog_flag(gc_margin, 1000000) or more. Default is 1000 (kB).
***********************************************************************************************/
get_all_constraints(Constraints) :-
    findall(Constraint, smt_constraint(Constraint, _), Constraints),
    findall(Var_List, smt_constraint(_, Var_List), Var_Matrix),
    maplist(term_variables, Constraints, Term_Variable_Matrix),
    Term_Variable_Matrix = Var_Matrix.



/**********************************************************************************************
 * name_variables(Vars, Grounded_VAR_List, Unasserted_Vars)
 *  is used for naming variables in order to be able to 
 *  assert smt_constraints, while preserving and identifying 
 *  corresponding variables. 
 *  
 * Vars is a list of Variables.
 * 
 * Grounded_VAR_List is a list of variables of form: ['VAR'('_289')], 
 * where _289 is the original variable's address.
 * Unasserted_Vars is a list of form: ['_891', ...].
 * It contains all variables in Vars that are not asserted yet.
 **********************************************************************************************/
name_variables(Vars, Grounded_VAR_List, Unasserted_Vars) :-
    maplist(write_to_codes, Vars, Codelist),
    maplist(name_maplist, Codelist, Atomlist),
    name_variables_aux(Codelist, Atomlist, Grounded_VAR_List, Unasserted_Vars).
name_variables_aux([], [], [], []) :- !.
name_variables_aux([VarCode|VarCodes], [VarAtom|VarAtoms], ['VAR'(VarAtom)|Grounded_VAR_List], Unasserted_Vars) :-
    var(VarCode, VarAtom), !,
    name_variables_aux(VarCodes, VarAtoms, Grounded_VAR_List, Unasserted_Vars).
name_variables_aux([_|VarCodes], [VarAtom|VarAtoms], [V|Grounded_VAR_List], [VarAtom|Unasserted_Vars]) :-
    % backtracking means, Var has not been asserted yet.
    V = 'VAR'(VarAtom),
    name_variables_aux(VarCodes, VarAtoms, Grounded_VAR_List, Unasserted_Vars).



%'VAR'(Atom, 'VAR'(Atom)).


/**********************************************************************************************
 * name_maplist(Codes, Atom).
 * True if name(Atom, Codes) is true.
 *
 * Used for calling name from maplist.
***********************************************************************************************/
name_maplist(Codes, Atom) :-
    name(Atom, Codes).



/**********************************************************************************************
 * smt_retractall(Constraints, Vars).
 * Constraints is a list of all previously asserted smt_constraints.
 * Vars is a list of all previously asserted vars.
 *
 * True if all smt_constraint, var and var_bool have been succesfully retracted.
***********************************************************************************************/
smt_retractall(Constraints, Vars) :-
    findall((X, Var_List), smt_constraint(X, Var_List), Constraints),
    findall((X,Y), var(X,Y), Vars),
    retractall(smt_constraint(_,_)),
    retractall(var(_,_)),
    retractall(var_bool(_,_,_)).



/**********************************************************************************************
 * smt_declare_vars(Var_Codes_List, Sort, Var_Declaration_String)
 * Var_Codes_List is a list of code lists that each represent an identifier of a variable.
 * clpfd_smt uses memory addresses as identifiers.
 * 
 * If Var_Atom = '_891', then equivalent Var_Code = [95,56,57,49] = "_891".
 *      => Var_Codes_List = [[95,56,57,49] | Tail]
 * 
 * Sort is a code list representing a SMT-LIB2 sort. 
 * Such as "Bool" or "Int"
 * 
 * Var_Declaration_String is the resulting concationation of all var declarations.
 * A single var declaration is of the form:
 *      "(declare-const Var_Code () Sort)"
 *
 * smt_declare_vars can be used when trying to translate constraint to text files, 
 * rather than feed them to a smt-solver. (z3-API provides ways to declare constants without smtlib2 strings.)
 * Inspired by SWiPrologZ3, refactored.
 * 
 * Strings are APPENDED in REVERSE order for performance reasons.
 * Further Performance improvements might be achievable with difference lists.
***********************************************************************************************/
smt_declare_vars(Var_Codes_List, Sort, Var_Declaration_String) :-
    smt_declare_vars_aux(Var_Codes_List, Sort, "", Var_Declaration_String).

smt_declare_vars_aux([], _, Final_String, Final_String) :- !.
smt_declare_vars_aux([Var_Code|Tail], Sort, Var_Declaration_String_Acc, Var_Declaration_String) :-
    smt_var_declaration(Var_Code, Sort, Declaration_String),
    append(Declaration_String, Var_Declaration_String_Acc, Temp),
    smt_declare_vars_aux(Tail, Sort, Temp, Var_Declaration_String).

smt_var_declaration(Var_Code, Sort, Declaration_String) :-
    append("(declare-fun ", Var_Code, T0),
    append(" () ", Sort, T1),
    append(T1, ")\n", T2),              % newline code is conventional. Not strictly necessary.
    append(T0, T2, Declaration_String).


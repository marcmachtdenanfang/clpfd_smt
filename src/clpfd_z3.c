#include <stdio.h>
#include <stdlib.h>
#include <sicstus/sicstus.h>
#include <z3.h>
#include "clpfd_z3_glue.h"


#define LOG_Z3_CALLS

#ifdef LOG_Z3_CALLS
#define LOG_MSG(msg) Z3_append_log(msg)
#else
#define LOG_MSG(msg) ((void)0)
#endif

void set_logic(char const * s);
void exitf(const char* message);
void check_aux();
void check(Z3_context ctx, Z3_solver s, Z3_lbool expected_result);
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty);
Z3_ast mk_int_var(Z3_context ctx, const char * name);
Z3_ast mk_int(Z3_context ctx, int v);

/* global variables */
Z3_context ctx;
Z3_solver solver;
Z3_tactic solver_tactic = NULL;
Z3_symbol    *names = NULL;
Z3_func_decl *decls = NULL;
Z3_symbol solver_logic;
int current_var = 0;
Z3_model solver_model = 0;


/*
    names consists of the identifiers of declared variables.
    decls consists of the declarations of functions.
    Variables are uninterpreted functions and thus are included in decls.

    These auxiliary arrays are necessary when using Z3_parse_smtlib2_string
*/
void init_auxiliary_arrays(SP_integer amount)
{
    names = malloc(amount * sizeof(Z3_symbol));
    decls = malloc(amount * sizeof(Z3_func_decl));
    if(names == NULL || decls == NULL)
    {
        exitf("Initializing the auxiliary arrays \"names\" and \"decls\" went wrong.");
    }
}


/*
    initialize context. 
    Solver needs to be created specifically.
    The predicate option_handler in clpfd_z3.pl creates the solver.
    If you decide to create the solver on your own, run: assert(solver_is_initialized).
    That way option_handler will not create a new solver.
*/
void init()
{
    Z3_config cfg;

    cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "model", "true");

    ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
}

void mk_solver_from_tactic(char const * str)
{
    
    solver_tactic = Z3_mk_tactic(ctx, str);
    Z3_tactic_inc_ref(ctx, solver_tactic);

    solver = Z3_mk_solver_from_tactic(ctx, solver_tactic);
    Z3_solver_inc_ref(ctx, solver);
    
}

void mk_solver_for_logic(char const * logic)
{
    Z3_symbol str = Z3_mk_string_symbol(ctx, logic);
    solver = Z3_mk_solver_for_logic(ctx, str);
    Z3_solver_inc_ref(ctx, solver);
}


/* 
    e.g. Z3_global_param_set("parallel.enable", "true");
    
    do NOT set parallel.enable = true when using LIA!
        => returns massive performance penalty (even though counter-intuitive).
*/
void set_global_parameters(char const * param_id, char const * param_value)
{
    Z3_global_param_set(param_id, param_value);
}


/*
    kill solver/context
*/
void delete_solver()
{
    if(solver_tactic != NULL) Z3_tactic_dec_ref(ctx, solver_tactic);
    if(solver_logic  != NULL) solver_logic == NULL;
    if(solver_model  != 0) {
        Z3_model_dec_ref(ctx, solver_model);
        solver_model = 0;
    }
    Z3_solver_reset(ctx, solver);
    Z3_solver_dec_ref(ctx, solver);
}

void delete_context()
{
    // apparently delete_solver frees these arrays. 
    // Maybe there is a very intransparent side effect in one of those functions.
    //if(names != NULL) free(names);
    //if(decls != NULL) free(decls);
    current_var = 0;
    Z3_del_context(ctx);
    Z3_global_param_reset_all();
}


void declare_int(char const * varname)
{
    Z3_sort int_sort;
    Z3_symbol int_symbol;
    Z3_ast variable;

    int_sort = Z3_mk_int_sort(ctx);
    int_symbol = Z3_mk_string_symbol(ctx, varname);

    variable = Z3_mk_const(ctx, int_symbol, int_sort);

    decls[current_var] = Z3_get_app_decl(ctx, Z3_to_app(ctx, variable));
    names[current_var] = int_symbol;
    current_var++;
}


// integer_variant is already declared
void declare_bool(char const * varname, char const * integer_variant)
{
    Z3_sort bool_sort;
    Z3_symbol bool_symbol;
    Z3_ast bool_var, int_var, one, zero, bool_to_int;
    
    bool_sort   = Z3_mk_bool_sort(ctx);
    bool_symbol = Z3_mk_string_symbol(ctx, varname);
    bool_var    = Z3_mk_const(ctx, bool_symbol, bool_sort);

    int_var     = mk_int_var(ctx, integer_variant);
    one         = mk_int(ctx, 1);
    zero        = mk_int(ctx, 0);
    
    bool_to_int = Z3_mk_eq(ctx, Z3_mk_ite(ctx, bool_var, one, zero), int_var);
    // printf("term: %s\n", Z3_ast_to_string(ctx, bool_to_int));

    decls[current_var] = Z3_get_app_decl(ctx, Z3_to_app(ctx, bool_var));
    names[current_var] = bool_symbol;
    current_var++;
    Z3_solver_assert(ctx, solver, bool_to_int);
}


void parse_assertion(char const * smt_assertions)
{
    Z3_ast_vector assertions;
    assertions = Z3_parse_smtlib2_string(ctx, smt_assertions, 0,0,0, current_var, names, decls);
    for (int i = 0; i < Z3_ast_vector_size(ctx, assertions); ++i) {
        Z3_solver_assert(ctx, solver, Z3_ast_vector_get(ctx, assertions, i));
    }
    //printf("Solver: %s\n", Z3_solver_to_string(ctx, solver));
}


/* 
 * Printing the solver after check_sat yields 
 * very interesting insights into the internals of Z3!
 * Only do that on a small benchmark.
 */
SP_atom check_sat()
{
    Z3_lbool result = Z3_solver_check(ctx, solver);
    switch (result) {
        case Z3_L_TRUE:
            // printf("sat\n");
            // printf("Solver: %s\n", Z3_solver_to_string(ctx, solver));
            return SP_atom_from_string("true");
        case Z3_L_FALSE:
            printf("unsat\n");
            // printf("Solver: %s\n", Z3_solver_to_string(ctx, solver));
            return SP_atom_from_string("false");
        case Z3_L_UNDEF:
            printf("unknown\n");
            return SP_atom_from_string("false");
    }
    printf("Z3_solver_check or the switch-statement in \"SP_atom check_sat()\" might be broken. \n");
    return SP_atom_from_string("false");
    // check(ctx, solver, Z3_L_TRUE);
    // Z3_stats stats = Z3_solver_get_statistics(ctx, solver);
    // printf("Statistics:\n%s\n", Z3_stats_to_string(ctx, stats));
    // printf("Solver: %s\n", Z3_solver_to_string(ctx, solver));
}

void init_solver_model()
{
    solver_model = Z3_solver_get_model(ctx, solver);
    if(solver_model != 0) Z3_model_inc_ref(ctx, solver_model);
}

void dec_solver_model()
{
    if (solver_model) Z3_model_dec_ref(ctx, solver_model);
}


SP_integer get_value(char const * var_name)
{
    int return_value;
    Z3_ast v;

    Z3_ast variable = mk_int_var(ctx, var_name);
    if(Z3_model_eval(ctx, solver_model, variable, 1, &v) != 0)
    {
        Z3_get_numeral_int(ctx, v, &return_value);
    } else
    {
        char buffer[40];
        strcpy(buffer, "Failed to evaluate: ");
        strcat(buffer, var_name);
        exitf(buffer);
    }
    return return_value;
}





/********************************************************************/
/* 
    All the following functions are taken from 
        /Path/to/z3/examples/c/test_capi.c
    that are supplied by the z3-4.8.9 distribution.

    Code examples are adapted to use with global context and 
    global solver definitions.
*/
/********************************************************************/





/**
  \brief Demonstrates how to initialize the parser symbol table.
*/
void parser_example()
{
    Z3_ast x, y;
    Z3_symbol         names[2];
    Z3_func_decl decls[2];
    Z3_ast_vector f;
    unsigned i;

    printf("\nparser_example2\n");
    LOG_MSG("parser_example2");


    /* Z3_enable_arithmetic doesn't need to be invoked in this example
       because it will be implicitly invoked by mk_int_var.
    */

    x        = mk_int_var(ctx, "x");
    decls[0] = Z3_get_app_decl(ctx, Z3_to_app(ctx, x));
    y        = mk_int_var(ctx, "y");
    decls[1] = Z3_get_app_decl(ctx, Z3_to_app(ctx, y));

    names[0] = Z3_mk_string_symbol(ctx, "a");
    names[1] = Z3_mk_string_symbol(ctx, "b");

    f = Z3_parse_smtlib2_string(ctx,
                           "(assert (> a b))",
                           0, 0, 0,
                           /* 'x' and 'y' declarations are inserted as 'a' and 'b' into the parser symbol table. */
                           2, names, decls);
    printf("formula: %s\n", Z3_ast_vector_to_string(ctx, f));
    printf("assert axiom:\n%s\n", Z3_ast_vector_to_string(ctx, f));
    for (i = 0; i < Z3_ast_vector_size(ctx, f); ++i) {
        Z3_solver_assert(ctx, solver, Z3_ast_vector_get(ctx, f, i));
    }
    check(ctx, solver, Z3_L_TRUE);
}


/**
   \brief Find a model for <tt>x < y + 1, x > 2</tt>.
   Then, assert <tt>not(x = y)</tt>, and find another model.
*/
void find_model_example2()
{
    Z3_ast x, y, one, two, y_plus_one;
    Z3_ast x_eq_y;
    Z3_ast args[2];
    Z3_ast c1, c2, c3;

    printf("\nfind_model_example2\n");
    LOG_MSG("find_model_example2");

    //ctx        = mk_context();
    init();
    solver     = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);

    x          = mk_int_var(ctx, "x");
    y          = mk_int_var(ctx, "y");
    one        = mk_int(ctx, 1);
    two        = mk_int(ctx, 2);

    args[0]    = y;
    args[1]    = one;
    y_plus_one = Z3_mk_add(ctx, 2, args);

    c1         = Z3_mk_lt(ctx, x, y_plus_one);
    c2         = Z3_mk_gt(ctx, x, two);

    Z3_solver_assert(ctx, solver, c1);
    Z3_solver_assert(ctx, solver, c2);

    printf("model for: x < y + 1, x > 2\n");
    check(ctx, solver, Z3_L_TRUE);

    /* assert not(x = y) */
    x_eq_y     = Z3_mk_eq(ctx, x, y);
    c3         = Z3_mk_not(ctx, x_eq_y);
    Z3_solver_assert(ctx, solver, c3);

    printf("model for: x < y + 1, x > 2, not(x = y)\n");
    check(ctx, solver, Z3_L_TRUE);

    delete_solver();
    delete_context();
}


/********************************************************************/

/**
   \brief exit gracefully in case of error.
*/
void exitf(const char* message)
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief Create a variable using the given name and type.
*/
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol symbol = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, symbol, ty);
}

Z3_ast mk_int_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create a Z3 integer node using a C int.
*/
Z3_ast mk_int(Z3_context ctx, int v)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return Z3_mk_int(ctx, v, ty);
}

/**
   \brief Check whether the logical context is satisfiable, and compare the result with the expected result.
   If the context is satisfiable, then display the model.
*/
void check(Z3_context ctx, Z3_solver s, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_solver_check(ctx, s);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        break;
    case Z3_L_TRUE:
        m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        printf("sat\n%s\n", Z3_model_to_string(ctx, m));
        break;
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
    if (m) Z3_model_dec_ref(ctx, m);
}



-module( cf_reference_test ).

-include_lib( "eunit/include/eunit.hrl" ).

-import( cf_reference, [arg_ntv/3, arg_frn/2, bind/2, str/1, file/1,
                        lambda_ntv/2, lambda_frn/5, app/2, fut/1, true/0,
                        false/0, cnd/3] ).
-import( cf_reference, [t_arg/2, t_str/0, t_file/0, t_bool/0, t_fn/3] ).
-import( cf_reference, [l_bash/0] ).
-import( cf_reference, [is_value/1, type/2, step/1, eval/1] ).
-import( cf_reference, [gensym/1, rename/3, subst/3] ).


-define( E_LAMBDA1, lambda_ntv( [arg_ntv( x, "x", t_str() ),
                                      arg_ntv( y, "y", t_file() )], x ) ).

-define( E_LAMBDA_FIRST, lambda_ntv( [arg_ntv( x, "x", t_str() ),
                                      arg_ntv( y, "y", t_str() )], x ) ).

-define( E_LAMBDA_CONST, lambda_ntv( [], str( "blub" ) ) ).

-define( E_LAMBDA_ID, lambda_ntv( [arg_ntv( x, "x", t_str() )], x ) ).

-define( E_APP_ID, app( ?E_LAMBDA_ID, [bind( "x", str( "blub" ) )] ) ).

-define( E_LAMBDA_GREET, lambda_frn( "greet", [arg_frn( "name", t_str() )],
                                     t_str(), l_bash(), "shalala" ) ).

-define( E_APP_GREET, app( ?E_LAMBDA_GREET,
                           [bind( "name", str( "flimbim" ) )] ) ).

-define( E_IF, cnd( true(), str( "bla" ), str( "blub" ) ) ).


is_value_test_() ->
  {foreach,

   fun() -> ok end,
   fun( _ ) -> ok end,

   [
    {"str is value",            fun str_is_value/0},
    {"file is value",           fun file_is_value/0},
    {"variable is no value",    fun variable_is_no_value/0},    
    {"abstraction is value",    fun abstraction_is_value/0},
    {"application is no value", fun application_is_no_value/0},
    {"future is no value",      fun future_is_no_value/0},
    {"boolean is value",        fun boolean_is_value/0},
    {"condition is no value",   fun condition_is_no_value/0}
   ]
  }.


str_is_value() ->
  ?assert( is_value( str( "blub" ) ) ).

file_is_value() ->
  ?assert( is_value( file( "bla" ) ) ).

variable_is_no_value() ->
  ?assertNot( is_value( x ) ).

abstraction_is_value() ->
  ?assert( is_value( ?E_LAMBDA1 ) ),
  ?assert( is_value( ?E_LAMBDA_FIRST ) ),
  ?assert( is_value( ?E_LAMBDA_CONST ) ),
  ?assert( is_value( ?E_LAMBDA_ID ) ),
  ?assert( is_value( ?E_LAMBDA_GREET ) ).

application_is_no_value() ->
  ?assertNot( is_value( ?E_APP_ID ) ),
  ?assertNot( is_value( ?E_APP_GREET ) ).

future_is_no_value() ->
  ?assertNot( is_value( fut( ?E_APP_GREET ) ) ).

boolean_is_value() ->
  ?assert( is_value( true() ) ),
  ?assert( is_value( false() ) ).

condition_is_no_value() ->
  ?assertNot( is_value( ?E_IF ) ).


type_test_() ->
  {foreach,

   fun() -> ok end,
   fun( _ ) -> ok end,

   [
    {"str typable",                fun str_typable/0},
    {"file typable",               fun file_typable/0},
    {"unbound variable untypable", fun unbound_variable_untypable/0},
    {"bound variable typable",     fun bound_variable_typable/0},
    {"native function typable",    fun native_function_typable/0},
    {"foreign function typable",   fun foreign_function_typable/0},

    {"native function with untypable body untypable",
     fun native_function_with_untypable_body_untypable/0},

    {"native function accessing its closure typable",
     fun native_function_accessing_its_closure_typable/0},

    {"application typable",        fun application_typable/0},

    {"application with untypable function expression untypable",
     fun application_with_untypable_function_expression_untypable/0},

    {"application whose function expression accesses closure typable",
     fun application_whose_function_expression_accesses_closure_typable/0},

    {"application with untypable argument untypable",
     fun application_with_untypable_argument_untypable/0},

    {"application whose argument expression accesses closure typable",
     fun application_whose_argument_expression_accesses_closure_typable/0},

    {"application with nonmatching argument term untypable",
     fun application_with_nonmatching_argument_term_untypable/0},

    {"application with one argument short untypable",
     fun application_with_one_argument_short_untypable/0},

    {"application with one argument too much untypable",
     fun application_with_one_argument_too_much_untypable/0},

    {"application with wrong keyword untypable",
     fun application_with_wrong_keyword_untypable/0},

    {"application with arguments in wrong order untypable",
     fun application_with_arguments_in_wrong_order_untypable/0},

    {"application with foreign function typable",
     fun application_with_foreign_function_typable/0},

    {"future typable",             fun future_typable/0},

    {"bool can be return type of foreign function",
     fun bool_can_be_return_type_of_foreign_function/0},

    {"true typable",               fun true_typable/0},
    {"false typable",              fun false_typable/0},
    {"condition typable",          fun condition_typable/0},

    {"condition untypable if conditional expr not bool",
     fun condition_untypable_if_conditional_expr_not_bool/0},

    {"condition untypable if conditional expr untypable",
     fun condition_untypable_if_conditional_expr_untypable/0},

    {"condition typable if conditional expr accesses closure",
     fun condition_typable_if_conditional_expr_accesses_closure/0},

    {"condition untypable if then and else expression types unequal",
     fun condition_untypable_if_then_and_else_expression_types_unequal/0},

    {"condition untypable if then expression untypable",
     fun condition_untypable_if_then_expression_untypable/0},

    {"condition typable if then expression accesses closure",
     fun condition_typable_if_then_expression_accesses_closure/0},

    {"condition untypable if else expression untypable",
     fun condition_untypable_if_else_expression_untypable/0},

    {"condition typable if else expression accesses closure",
     fun condition_typable_if_else_expression_accesses_closure/0}
   ]
  }.

str_typable() ->
  ?assertEqual( {ok, t_str()}, type( #{}, str( "bla" ) ) ).

file_typable() ->
  ?assertEqual( {ok, t_file()}, type( #{}, file( "blub" ) ) ).

unbound_variable_untypable() ->
  ?assertEqual( error, type( #{}, x ) ).

bound_variable_typable() ->
  ?assertEqual( {ok, t_str()}, type( #{ x => t_str() }, x ) ).

native_function_typable() ->

  T1 = t_fn( ntv, [t_arg( "x", t_str() ), t_arg( "y", t_file() )], t_str() ),
  ?assertEqual( {ok, T1}, type( #{}, ?E_LAMBDA1 ) ),

  T2 = t_fn( ntv, [t_arg( "x", t_str() ), t_arg( "y", t_str() )], t_str() ),
  ?assertEqual( {ok, T2}, type( #{}, ?E_LAMBDA_FIRST ) ),

  T3 = t_fn( ntv, [], t_str() ),
  ?assertEqual( {ok, T3}, type( #{}, ?E_LAMBDA_CONST ) ),

  T4 = t_fn( ntv, [t_arg( "x", t_str() )], t_str() ),
  ?assertEqual( {ok, T4}, type( #{}, ?E_LAMBDA_ID ) ).

foreign_function_typable() ->
  T = t_fn( frn, [t_arg( "name", t_str() )], t_str() ),
  ?assertEqual( {ok, T}, type( #{}, ?E_LAMBDA_GREET ) ).

native_function_with_untypable_body_untypable() ->
  ?assertEqual( error, type( #{}, lambda_ntv( [], x ) ) ).

native_function_accessing_its_closure_typable() ->
  T = t_fn( ntv, [], t_str() ),
  ?assertEqual( {ok, T}, type( #{ x => t_str() }, lambda_ntv( [], x ) ) ).

application_typable() ->
  ?assertEqual( {ok, t_str()}, type( #{}, ?E_APP_ID ) ),
  ?assertEqual( {ok, t_str()}, type( #{}, ?E_APP_GREET ) ).

application_with_untypable_function_expression_untypable() ->
  ?assertEqual( error, type( #{}, app( f, [bind( "x", str( "blub" ) )] ) ) ).

application_whose_function_expression_accesses_closure_typable() ->
  Gamma = #{ f => t_fn( ntv, [t_arg( "x", t_str() )], t_file() )},
  E = app( f, [bind( "x", str( "blub" ) )] ),
  T = t_file(),
  ?assertEqual( {ok, T}, type( Gamma, E ) ).

application_with_untypable_argument_untypable() ->
  ?assertEqual( error, type( #{}, app( ?E_LAMBDA_ID, [bind( "x", x )] ) ) ).

application_whose_argument_expression_accesses_closure_typable() ->
  Gamma = #{ x => t_str() },
  E = app( ?E_LAMBDA_ID, [bind( "x", x )] ),
  T = t_str(),
  ?assertEqual( {ok, T}, type( Gamma, E ) ).

application_with_nonmatching_argument_term_untypable() ->
  E = app( ?E_LAMBDA_ID, [bind( "x", ?E_LAMBDA_ID )] ),
  ?assertEqual( error, type( #{}, E ) ).

application_with_one_argument_short_untypable() ->

  E1 = app( ?E_LAMBDA1, [bind( "x", str( "blub" ) )] ),
  ?assertEqual( error, type( #{}, E1 ) ),

  E2 = app( ?E_LAMBDA1, [bind( "y", file( "blub" ) )] ),
  ?assertEqual( error, type( #{}, E2 ) ),

  E3 = app( ?E_LAMBDA1, [] ),
  ?assertEqual( error, type( #{}, E3 ) ).

application_with_one_argument_too_much_untypable() ->

  E1 = app( ?E_LAMBDA_ID, [bind( "x", str( "blub" ) ),
                           bind( "y", file( "blub" ) )] ),
  ?assertEqual( error, type( #{}, E1 ) ),

  E2 = app( ?E_LAMBDA1, [bind( "x", str( "blub" ) ),
                         bind( "y", file( "blub" ) ),
                         bind( "z", str( "blub" ) )] ),
  ?assertEqual( error, type( #{}, E2 ) ).

application_with_wrong_keyword_untypable() ->

  E1 = app( ?E_LAMBDA_ID, [bind( "y", str( "blub" ) )] ),
  ?assertEqual( error, type( #{}, E1 ) ),

  E2 = app( ?E_LAMBDA1, [bind( "x", str( "blub" ) ),
                         bind( "z", file( "blub" ) )] ),
  ?assertEqual( error, type( #{}, E2 ) ),

  E3 = app( ?E_LAMBDA1, [bind( "z", str( "blub" ) ),
                         bind( "y", file( "blub" ) )] ),
  ?assertEqual( error, type( #{}, E3 ) ).

application_with_arguments_in_wrong_order_untypable() ->

  E = app( ?E_LAMBDA1, [bind( "y", file( "blub" ) ),
                        bind( "x", str( "blub" ) )] ),
  ?assertEqual( error, type( #{}, E ) ).

application_with_foreign_function_typable() ->
  ?assertEqual( {ok, t_str()}, type( #{}, ?E_APP_GREET ) ).

future_typable() ->
  ?assertEqual( {ok, t_str()}, type( #{}, fut( ?E_APP_GREET ) ) ).

bool_can_be_return_type_of_foreign_function() ->
  T = t_fn( frn, [], t_bool() ),
  E = lambda_frn( "test", [], t_bool(), l_bash(), "lala" ),
  ?assertEqual( {ok, T}, type( #{}, E ) ).

true_typable() ->
  ?assertEqual( {ok, t_bool()}, type( #{}, true() ) ).

false_typable() ->
  ?assertEqual( {ok, t_bool()}, type( #{}, false() ) ).

condition_typable() ->
  ?assertEqual( {ok, t_str()}, type( #{}, ?E_IF ) ).

condition_untypable_if_conditional_expr_not_bool() ->
  E = cnd( str( "blub" ), str( "bla" ), str( "shalala" ) ),
  ?assertEqual( error, type( #{}, E ) ).

condition_untypable_if_conditional_expr_untypable() ->
  E = cnd( x, str( "bla" ), str( "shalala" ) ),
  ?assertEqual( error, type( #{}, E ) ).

condition_typable_if_conditional_expr_accesses_closure() ->
  Gamma = #{ x => t_bool() },
  E = cnd( x, str( "bla" ), str( "shalala" ) ),
  ?assertEqual( {ok, t_str()}, type( Gamma, E ) ).

condition_untypable_if_then_and_else_expression_types_unequal() ->
  E = cnd( true(), str( "bla" ), file( "blub" ) ),
  ?assertEqual( error, type( #{}, E ) ).

condition_untypable_if_then_expression_untypable() ->
  E = cnd( true(), x, str( "blub" ) ),
  ?assertEqual( error, type( #{}, E ) ).

condition_typable_if_then_expression_accesses_closure() ->
  Gamma = #{ x => t_str() },
  E = cnd( true(), x, str( "blub" ) ),
  ?assertEqual( {ok, t_str()}, type( Gamma, E ) ).

condition_untypable_if_else_expression_untypable() ->
  E = cnd( true(), str( "blub" ), x ),
  ?assertEqual( error, type( #{}, E ) ).

condition_typable_if_else_expression_accesses_closure() ->
  Gamma = #{ x => t_str() },
  E = cnd( true(), str( "blub" ), x ),
  ?assertEqual( {ok, t_str()}, type( Gamma, E ) ).


gensym_test_() ->
  {foreach,

   fun() -> ok end,
   fun( _ ) -> ok end,

   [
    {"gensym adds unique number to var",
     fun gensym_adds_unique_number_to_var/0},

    {"gensym replaces unique number instead of appending",
     fun gensym_replaces_unique_number_instead_of_appending/0}
   ]
  }.

gensym_adds_unique_number_to_var() ->
  X = gensym( blub ),
  [A, _] = string:tokens( atom_to_list( X ), "$" ),
  ?assertEqual( "blub", A ).

gensym_replaces_unique_number_instead_of_appending() ->
  X1 = gensym( blub ),
  X2 = gensym( X1 ),
  [A, _] = string:tokens( atom_to_list( X2 ), "$" ),
  ?assertEqual( "blub", A ).


rename_test_() ->
  {foreach,

   fun() -> ok end,
   fun( _ ) -> ok end,

   [
    {"rename leaves str unchanged",   fun rename_leaves_str_unchanged/0},
    {"rename leaves file unchanged",  fun rename_leaves_file_unchanged/0},
    {"rename leaves true unchanged",  fun rename_leaves_true_unchanged/0},
    {"rename leaves false unchanged", fun rename_leaves_false_unchanged/0},
    {"rename alters matching var",    fun rename_alters_matching_var/0},

    {"rename leaves mismatching var unchanged",
     fun rename_leaves_mismatching_var_unchanged/0},

    {"rename leaves native function mismatching name unchanged",
     fun rename_leaves_native_function_mismatching_name_unchanged/0},

    {"rename alters native function arg list",
     fun rename_alters_native_function_arg_list/0},

    {"rename alters native function body",
     fun rename_alters_native_function_body/0},

    {"rename leaves foreign function unchanged",
     fun rename_leaves_foreign_function_unchanged/0},

    {"rename traverses application function expr",
     fun rename_traverses_application_function_expr/0},

    {"rename traverses application binding list",
     fun rename_traverses_application_binding_list/0},

    {"rename leaves fut unchanged",   fun rename_leaves_fut_unchanged/0},

    {"rename traverses condition if expr",
     fun rename_traverses_condition_if_expr/0},

    {"rename traverses condition then expr",
     fun rename_traverses_condition_then_expr/0},

    {"rename traverses condition else expr",
     fun rename_traverses_condition_else_expr/0}
   ]
  }.

rename_leaves_str_unchanged() ->
  E = str( "bla" ),
  ?assertEqual( E, rename( E, x, y ) ).

rename_leaves_file_unchanged() ->
  E = file( "bla" ),
  ?assertEqual( E, rename( E, x, y ) ).

rename_leaves_true_unchanged() ->
  E = true(),
  ?assertEqual( E, rename( E, x, y ) ).

rename_leaves_false_unchanged() ->
  E = false(),
  ?assertEqual( E, rename( E, x, y ) ).

rename_alters_matching_var() ->
  ?assertEqual( y, rename( x, x, y ) ).

rename_leaves_mismatching_var_unchanged() ->
  ?assertEqual( x, rename( x, y, z ) ).

rename_leaves_native_function_mismatching_name_unchanged() ->
  ?assertEqual( lambda_ntv( [arg_ntv( a, "a", t_str() )], x ),
                rename( lambda_ntv( [arg_ntv( a, "a", t_str() )], x ), b, c ) ).

rename_alters_native_function_arg_list() ->
  ?assertEqual( lambda_ntv( [arg_ntv( b, "a", t_str() )], x ),
                rename( lambda_ntv( [arg_ntv( a, "a", t_str() )], x ), a, b ) ).

rename_alters_native_function_body() ->
  ?assertEqual( lambda_ntv( [], y ), rename( lambda_ntv( [], x ), x, y ) ).

rename_leaves_foreign_function_unchanged() ->
  E = ?E_LAMBDA_GREET,
  ?assertEqual( E, rename( E, x, y ) ).

rename_traverses_application_function_expr() ->
  E = app( lambda_ntv( [], x ), [] ),
  ?assertEqual( app( lambda_ntv( [], y ), [] ), rename( E, x, y ) ).

rename_traverses_application_binding_list() ->
  F = lambda_ntv( [arg_ntv( x, "x", t_str() )], x ),
  E = app( F, [bind( "x", y )] ),
  ?assertEqual( app( F, [bind( "x", z )] ), rename( E, y, z ) ).

rename_leaves_fut_unchanged() ->
  E = fut( ?E_APP_GREET ),
  ?assertEqual( E, rename( E, x, y ) ).

rename_traverses_condition_if_expr() ->
  ?assertEqual( cnd( y, true(), false() ),
                rename( cnd( x, true(), false() ), x, y ) ).

rename_traverses_condition_then_expr() ->
  ?assertEqual( cnd( true(), y, false() ),
                rename( cnd( true(), x, false() ), x, y ) ).

rename_traverses_condition_else_expr() ->
  ?assertEqual( cnd( true(), true(), y ),
                rename( cnd( true(), true(), x ), x, y ) ).

subst_test_() ->
  {foreach,

   fun() -> ok end,
   fun( _ ) -> ok end,

   [
    {"subst leaves str unchanged",   fun subst_leaves_str_unchanged/0},
    {"subst leaves file unchanged",  fun subst_leaves_file_unchanged/0},
    {"subst leaves true unchanged",  fun subst_leaves_true_unchanged/0},
    {"subst leaves false unchanged", fun subst_leaves_false_unchanged/0},

    {"subst replaces if variable match",
     fun subst_replaces_if_variable_match/0},

    {"subst leaves unchanged if variable mismatch",
     fun subst_leaves_unchanged_if_variable_mismatch/0},

    {"subst continues in function expr of app",
     fun subst_continues_in_function_expr_of_app/0},

    {"subst continues in arg expr of app",
     fun subst_continues_in_arg_expr_of_app/0},

    {"subst continues in native function body",
     fun subst_continues_in_native_function_body/0},

    {"subst native function arg shadowed",
     fun subst_native_function_arg_shadowed/0},

    {"subst capture avoiding",       fun subst_capture_avoiding/0},

    {"subst leaves foreign function unchanged",
     fun subst_leaves_foreign_function_unchanged/0},

    {"subst leaves fut unchanged",   fun subst_leaves_fut_unchanged/0},

    {"subst traverses condition if expr",
     fun subst_traverses_condition_if_expr/0},

    {"subst traverses condition then expr",
     fun subst_traverses_condition_then_expr/0},

    {"subst traverses condition else expr",
     fun subst_traverses_condition_else_expr/0}
   ]
  }.

subst_leaves_str_unchanged() ->
  E = str( "bla" ),
  ?assertEqual( E, subst( E, x, y ) ).

subst_leaves_file_unchanged() ->
  E = file( "bla" ),
  ?assertEqual( E, subst( E, x, y ) ).

subst_leaves_true_unchanged() ->
  E = true(),
  ?assertEqual( E, subst( E, x, y ) ).

subst_leaves_false_unchanged() ->
  E = false(),
  ?assertEqual( E, subst( E, x, y ) ).

subst_replaces_if_variable_match() ->
  ?assertEqual( y, subst( x, x, y ) ).

subst_leaves_unchanged_if_variable_mismatch() ->
  ?assertEqual( x, subst( x, y, z ) ).

subst_continues_in_function_expr_of_app() ->
  ?assertEqual( app( y, [] ), subst( app( x, [] ), x, y ) ).

subst_continues_in_arg_expr_of_app() ->
  ?assertEqual( app( f, [bind( "x", y )] ),
                subst( app( f, [bind( "x", x )] ), x, y ) ).

subst_continues_in_native_function_body() ->
  ?assertMatch( {lambda, ntv, [], y}, subst( lambda_ntv( [], x ), x, y ) ),
  ?assertMatch( {lambda, ntv, [{_, "a", 'Str'}], y},
                subst( lambda_ntv( [{a, "a", t_str()}], x ), x, y ) ).

subst_native_function_arg_shadowed() ->
  ?assertEqual( ?E_LAMBDA_ID, subst( ?E_LAMBDA_ID, x, y ) ).

subst_capture_avoiding() ->
  E1 = lambda_ntv( [arg_ntv( y, "y", t_str() )], x ),
  E2 = subst( E1, x, y ),
  {lambda, ntv, [{A, "y", 'Str'}], B} = E2,
  ?assertNotEqual( A, B ).

subst_leaves_foreign_function_unchanged() ->
  E = ?E_LAMBDA_GREET,
  ?assertEqual( E, subst( E, x, y ) ).

subst_leaves_fut_unchanged() ->
  E = fut( ?E_APP_GREET ),
  ?assertEqual( E, subst( E, x, y ) ).

subst_traverses_condition_if_expr() ->
  ?assertEqual( cnd( y, true(), false() ),
                subst( cnd( x, true(), false() ), x, y ) ).

subst_traverses_condition_then_expr() ->
  ?assertEqual( cnd( true(), y, false() ),
                subst( cnd( true(), x, false() ), x, y ) ).

subst_traverses_condition_else_expr() ->
  ?assertEqual( cnd( true(), true(), y ),
                subst( cnd( true(), true(), x ), x, y ) ).


step_test_() ->
  {foreach,

   fun() -> ok end,
   fun( _ ) -> ok end,

   [
    {"str is left alone",               fun str_is_left_alone/0},
    {"file is left alone",              fun file_is_left_alone/0},
    {"future is left alone",            fun future_is_left_alone/0},
    {"true is left alone",              fun true_is_left_alone/0},
    {"false is left alone",             fun false_is_left_alone/0},

    {"native function body is left alone",
     fun native_function_body_is_left_alone/0},

    {"constant function evaluates value",
     fun constant_function_evaluates_value/0},

    {"identity function inserts arg", fun identity_function_inserts_arg/0}
   ]
  }.

str_is_left_alone() ->
  ?assertEqual( norule, step( str( "blub" ) ) ).

file_is_left_alone() ->
  ?assertEqual( norule, step( file( "blub" ) ) ).

future_is_left_alone() ->
  ?assertEqual( norule, step( fut( ?E_APP_GREET ) ) ).

true_is_left_alone() ->
  ?assertEqual( norule, step( true() ) ).

false_is_left_alone() ->
  ?assertEqual( norule, step( false() ) ).

native_function_body_is_left_alone() ->
  ?assertEqual( norule, step( lambda_ntv( [], ?E_IF ) ) ).

constant_function_evaluates_value() ->
  ?assertEqual( {ok, str( "blub" )}, step( app( ?E_LAMBDA_CONST, [] ) ) ).

identity_function_inserts_arg() ->
  ?assertEqual( {ok, app( lambda_ntv( [], str( "blub" ) ), [] )},
                step( ?E_APP_ID ) ).


eval_test_() ->
  {foreach,

   fun() -> ok end,
   fun( _ ) -> ok end,

   [
    {"identity function evaluates arg", fun identity_function_evaluates_arg/0},
    {"apply function ignoring arg", fun apply_function_ignoring_arg/0},

    {"evaluation continues in application function expr",
     fun evaluation_continues_in_application_function_expr/0},

    {"application arg is substituted as is",
     fun application_arg_is_substituted_as_is/0}
   ]
  }.

identity_function_evaluates_arg() ->
  ?assertEqual( str( "blub" ), eval( ?E_APP_ID ) ).

apply_function_ignoring_arg() ->

  E1 = app( lambda_ntv( [arg_ntv( x, "x", t_str() )],
                        app( ?E_LAMBDA_CONST, [] ) ),
            [bind( "x", str( "bla" ) )] ),
  ?assertEqual( str( "blub" ), eval( E1 ) ),

  E2 = app( lambda_ntv( [arg_ntv( x, "x", t_str() )],
                        str( "blub" ) ),
            [bind( "x", str( "bla" ) )] ),
  ?assertEqual( str( "blub" ), eval( E2 ) ),

  E3 = app( lambda_ntv( [arg_ntv( x, "x", t_str() )],
                        file( "blub" ) ),
            [bind( "x", str( "bla" ) )] ),
  ?assertEqual( file( "blub" ), eval( E3 ) ).

evaluation_continues_in_application_function_expr() ->
  E = app( app( ?E_LAMBDA_ID, [bind( "x", ?E_LAMBDA_CONST )]), [] ),
  ?assertEqual( str( "blub" ), eval( E ) ).

application_arg_is_substituted_as_is() ->
  E = app( ?E_LAMBDA_ID, [bind( "x", fut( ?E_APP_GREET ) )] ),
  ?assertEqual( fut( ?E_APP_GREET ), eval( E ) ).
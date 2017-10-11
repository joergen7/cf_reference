-module( cf_reference_test ).

-include_lib( "eunit/include/eunit.hrl" ).

-import( cf_reference, [arg_ntv/3, arg_frn/2, bind/2, str/1, file/1,
                        lambda_ntv/2, lambda_frn/5, app/2, fut/1, true/0,
                        false/0, cnd/3] ).
-import( cf_reference, [t_arg/2, t_str/0, t_file/0, t_bool/0, t_fn/3] ).
-import( cf_reference, [l_bash/0] ).
-import( cf_reference, [is_value/1, type/2, step/1] ).


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


step_test_() ->
  {foreach,

   fun() -> ok end,
   fun( _ ) -> ok end,

   [
    {"str is left alone",  fun str_is_left_alone/0},
    {"file is left alone", fun file_is_left_alone/0},

    {"native function body is left alone",
     fun native_function_body_is_left_alone/0},

    {"constant function evaluates value",
     fun constant_function_evaluates_value/0}
   ]
  }.

str_is_left_alone() ->
  ?assertEqual( norule, step( str( "blub" ) ) ).

file_is_left_alone() ->
  ?assertEqual( norule, step( file( "blub" ) ) ).

native_function_body_is_left_alone() ->
  ?assertEqual( norule, step( lambda_ntv( [], ?E_IF ) ) ).

constant_function_evaluates_value() ->
  ?assertEqual( {ok, str( "blub" )}, step( app( ?E_LAMBDA_CONST, [] ) ) ).

  
-module( cf_reference_test ).

-include_lib( "eunit/include/eunit.hrl" ).

-import( cf_reference, [arg_ntv/3, arg_frn/2, bind/2, str/1, file/1,
                        lambda_ntv/2, lambda_frn/5, app/2, fut/1, true/0,
                        false/0, cnd/3] ).
-import( cf_reference, [t_arg/2, t_str/0, t_file/0, t_fn/3] ).
-import( cf_reference, [l_bash/0] ).
-import( cf_reference, [is_value/1, type/2] ).


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
     fun application_whose_argument_expression_accesses_closure_typable/0}
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
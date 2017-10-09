-module( cf_reference_test ).

-include_lib( "eunit/include/eunit.hrl" ).

-import( cf_reference, [str/1, file/1, arg/3, lambda_ntv/2] ).
-import( cf_reference, [is_value/1] ).

-define( E_LAMBDA_FIRST, lambda_ntv( [arg( x, "x", 'Str' ),
                                      arg( y, "y", 'File' )], x ) ).

cf_reference_test_() ->
  {foreach,

   fun() -> ok end,

   fun( _ ) -> ok end,

   [
    {<<"str is a value">>,  fun str_is_value/0},
    {<<"file is a value">>, fun file_is_value/0},
    {<<"abstraction is a value">>, fun abstraction_is_value/0}
   ]
  }.


str_is_value() ->
  ?assert( is_value( str( "blub" ) ) ).

file_is_value() ->
  ?assert( is_value( file( "bla" ) ) ).

abstraction_is_value() ->
  ?assert( is_value( ?E_LAMBDA_FIRST ) ).

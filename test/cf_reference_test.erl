-module( cf_reference_test ).

-include_lib( "eunit/include/eunit.hrl" ).

-import( cf_reference, [str/1, file/1] ).
-import( cf_reference, [is_value/1] ).

cf_reference_test_() ->
  {foreach,

   fun() -> ok end,

   fun( _ ) -> ok end,

   [
    {<<"str is a value">>,  fun str_is_value/0},
    {<<"file is a value">>, fun file_is_value/0}
   ]
  }.


str_is_value() ->
  E = str( "blub" ),
  ?assert( is_value( E ) ).

file_is_value() ->
  E = file( "bla" ),
  ?assert( is_value( E ) ).
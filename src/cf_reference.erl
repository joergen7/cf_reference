%% -*- erlang -*-
%%
%% Cuneiform: A Functional Language for Large Scale Scientific Data Analysis
%%
%% Copyright 2016 Jörgen Brandt, Marc Bux, and Ulf Leser
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%    http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.

%% @author Jörgen Brandt <brandjoe@hu-berlin.de>

-module( cf_reference ).

-export( [as/2, let_bind/4, subst/3, free_vars/1] ).

-ifdef( TEST ).
-include_lib( "eunit/include/eunit.hrl" ).
-endif.

%%====================================================================
%% Abstract Syntax
%%====================================================================

%% Terms

-type tm()       :: var() | abs_nat() | abs_for() | app()
                  | fix() | zipwith()
                  | boolean() | cnd()
                  | str() | file()
                  | nl() | cons() | isnil()
                  | tup() | proj().

-type var()      :: {var, Name::string()}.

-type abs_nat()  :: {abs_nat, Sign::ctx(), Body::tm()}.

-type abs_for()  :: {abs_for, Sign::ctx(), RetTp::tp(), Lang::lang(),
                             Body::binary()}.

-type app()      :: {app, Left::tm(), Right:: arg_map()}.

-type fix()      :: {fix, Term::tm()}.

-type zipwith()  :: {zipwith, ArgLst::[string()], Term::tm()}.

-type cnd()      :: {cnd, IfTerm::tm(), ThenTerm::tm(), ElseTerm::tm()}.

-type str()      :: {str, string()}.

-type file()     :: {file, string()}.

-type nl()       :: {nl, Type::tp()}.

-type cons()     :: {cons, Type::tp(), Head::tm(), Tail::tm()}.

-type isnil()    :: {isnil, Type::tp(), Term::tm()}.

-type tup()      :: {tup, [tm()]}.

-type proj()     :: {proj, I::pos_integer(), Tuple::tm()}.


%% Types

-type tp()       :: tabs_nat() | tabs_for()
                  | tbool | tstr | tfile | tlst() | ttup().

-type utp()      :: tbool | tstr | tfile | tlst() | ttup().

-type ttup()     :: {ttup, [tp()]}.

-type tlst()     :: {tlst, tp()}.

-type tabs_nat() :: {tabs, nat, From::ctx(), To::tp()}.

-type tabs_for() :: {tabs, for, From::uctx(), To::utp()}.

%% Auxiliaries

-type lang()    :: bash | octave | perl | python | r.

-type arg_map() :: #{ string() => tm() }.

-type ctx()     :: #{ string => tp() }.

-type uctx()    :: #{ string => utp() }.


%%====================================================================
%% Derived Forms
%%====================================================================

%% @doc Ascription as derived form.

-spec as( Term::tm(), Type::tp() ) -> tm().

as( Tm, Tp ) ->
  X = fresh_name(),
  {app, {abs_nat, #{ X => Tp }, {var, X}}, #{ X => Tm }}.


%% @doc Let bindings as derived form.

-spec let_bind( X::string(), S::tm(), T::tm(), Ctx::ctx() ) -> tm().

let_bind( X, S, T, Ctx ) ->
  {app, {abs_nat, #{ X => type_of( S, Ctx ) }, T}, #{ X => S }}.
  
%%====================================================================
%% Substitution
%%====================================================================

%% @doc Substitutes free occurrences of a variable named `X` with `S` in a given
%%      term `T`.

-spec subst( X::string(), S::tm(), T::tm() ) -> tm().

subst( X, S, {var, X} )   ->
  S;

subst( _, _, T={var, _} ) ->
  T;

subst( X, S, {app, Left, Right} ) ->
  Left1 = subst( X, S, Left ),
  Right1 = maps:map( fun( _, V ) -> subst( X, S, V ) end, Right ),
  {app, Left1, Right1};

subst( X, S, T={abs_nat, Sign, _Body} ) ->
  
  BindLst = maps:keys( Sign ),

  T1 = case lists:member( X, BindLst ) of
         true  -> rename( X, T );
         false -> T
       end,

  FreeSet = free_vars( S ),

  F = fun( Y, Tin ) ->
        case sets:is_element( Y, FreeSet ) of
          false -> Tin;
          true  -> rename( Y, Tin )
        end
      end,

  T2 = lists:foldl( F, T1, BindLst ),

  {abs_nat, Sign2, Body2} = T2,

  {abs_nat, Sign2, subst( X, S, Body2)}.


%% @doc Extracts the set of variable names occurring free in a given term `T`.

-spec free_vars( T::tm() ) -> sets:set( string() ).

free_vars( {var, X} ) ->
  sets:add_element( X, sets:new() );

free_vars( {abs_nat, Sign, T1} ) ->
  F = fun( N, Fv ) -> sets:del_element( N, Fv ) end,
  lists:foldl( F, free_vars( T1 ), maps:keys( Sign ) );

free_vars( {abs_for, _, _, _, _} ) ->
  sets:new();

free_vars( {app, Left, Right} ) ->
  FvLeft = free_vars( Left ),
  FvRight = sets:union( [free_vars( X ) || X <- maps:values( Right )] ),
  sets:union( FvLeft, FvRight );

free_vars( {fix, T} ) ->
  free_vars( T );

free_vars( {zipwith, _, T} ) ->
  free_vars( T );

free_vars( true ) ->
  sets:new();

free_vars( false ) ->
  sets:new();

free_vars( {cnd, A, B, C} ) ->
  sets:union( [free_vars( A ), free_vars( B ), free_vars( C )] );

free_vars( {str, _} ) ->
  sets:new();

free_vars( {file, _} ) ->
  sets:new();

free_vars( {nl, _} ) ->
  sets:new();

free_vars( {cons, _, Head, Tail} ) ->
  sets:union( free_vars( Head ), free_vars( Tail ) );

free_vars( {isnil, _, T} ) ->
  free_vars( T );

free_vars( {tup, L} ) ->
  sets:union( [free_vars( X ) || X <- L] );

free_vars( {proj, _, T} ) ->
  free_vars( T ).


%% @doc consistently renames all occurrences of a given name `X` in the term
%%      `T`.

-spec rename( X::string(), T::tm() ) -> tm().

rename( X, T ) ->

  Renm = fun

        F( Y, {var, Y}, Fresh ) ->
          {var, Fresh};

        F( _, S={var, _}, _ ) ->
          S;

        F( Y, {abs_nat, Sign, Body}, Fresh ) ->
          Sign1 = case maps:is_key( Y, Sign ) of
                    false -> Sign;
                    true  ->
                      #{ Y := Tp} = Sign,
                      maps:put( Fresh, Tp, maps:remove( Y, Sign ) )
                  end,
          Body1 = F( Y, Body, Fresh ),
          {abs_nat, Sign1, Body1};

        F( Y, {abs_for, Sign, RetTp, Lang, Body}, Fresh ) ->
          Sign1 = case maps:is_key( Y, Sign ) of
                    false -> Sign;
                    true  ->
                      #{ Y := Tp } = Sign,
                      maps:put( Fresh, Tp, maps:remove( Y, Sign ) )
                  end,
          {abs_for, Sign1, RetTp, Lang, Body};

        F( Y, {app, Left, Right}, Fresh ) ->
          Left1 = F( Y, Left, Fresh ),
          Right1 = maps:map( fun( _, S ) -> F( Y, S, Fresh ) end, Right ),
          {app, Left1, Right1};

        F( Y, {fix, S}, Fresh ) ->
          {fix, F( Y, S, Fresh )};

        F( Y, {zipwith, ArgLst, S}, Fresh ) ->
          ArgLst1 = case lists:member( Y, ArgLst ) of
                      false -> ArgLst;
                      true  -> [Fresh|lists:delete( Y, ArgLst )]
                    end,
          {zipwith, ArgLst1, F( Y, S, Fresh )};

        F( _, true, _ ) ->
          true;

        F( _, false, _ ) ->
          false;

        F( Y, {cnd, If, Then, Else}, Fresh ) ->
          {cnd, F( Y, If, Fresh ), F( Y, Then, Fresh ), F( Y, Else, Fresh )};

        F( _, S={str, _}, _ ) ->
          S;

        F( _, S={file, _}, _ ) ->
          S;

        F( _, S={nl, _}, _) ->
          S;

        F( Y, {cons, Tp, S1, S2}, Fresh ) ->
          {cons, Tp, F( Y, S1, Fresh ), F( Y, S2, Fresh )};

        F( Y, {isnil, Tp, S}, Fresh ) ->
          {isnil, Tp, F( Y, S, Fresh )};

        F( Y, {tup, ElemLst}, Fresh ) ->
          {tup, [F( Y, Elem, Fresh ) || Elem <- ElemLst]};

        F( Y, {proj, I, S}, Fresh ) ->
          {proj, I, F( Y, S, Fresh )}

      end,

  Basename = case string:chr( X, $$ ) of
               0 -> X;
               I -> lists:sublist( X, I-1 )
             end,

  Fresh = Basename++fresh_name(),

  Renm( X, T, Fresh ).


%%====================================================================
%% Type Inference
%%====================================================================

%% @doc Infers the type of a term `T` by applying the inversion lemma.

-spec type_of( T::tm(), Ctx::ctx() ) -> tp().

type_of( {var, X}, Ctx ) ->
  #{ X := Tp } = Ctx,
  Tp;

type_of( {abs_for, _, RetTp, _, _}, _Ctx ) ->
  RetTp.


%%====================================================================
%% Internal Functions
%%====================================================================


%% @doc Generates a fresh name.

-spec fresh_name() -> string().

fresh_name() ->
  N = erlang:unique_integer( [positive, monotonic] ),
  [$$|integer_to_list( N )].



%%====================================================================
%% Unit Tests
%%====================================================================

-ifdef( TEST ).

%% Free Variables

var_is_free_test() ->
  ?assert( sets:is_element( "x", free_vars( {var, "x"} ) ) ).

identity_is_a_combinator_test() ->
  T = {abs_nat, #{ "x" => tbool }, {var, "x"}},
  ?assertEqual( 0, sets:size( free_vars( T ) ) ).

constant_var_fn_has_free_var_test() ->
  T = {abs_nat, #{ "x" => tbool }, {var, "y"}},
  ?assert( sets:is_element( "y", free_vars( T ) ) ).

foreign_abstraction_has_no_free_vars_test() ->
  T = {abs_for, #{}, tbool, bash, <<"blub">>},
  ?assertEqual( 0, sets:size( free_vars( T ) ) ).

app_gives_union_of_left_and_right_free_vars_test() ->
  Left = {var, "x"},
  Right = #{"y" => {var, "y"}, "z" => {var, "z"}},
  T = {app, Left, Right},
  ?assertEqual( 3, sets:size( free_vars( T ) ) ).

fix_is_neutral_to_free_vars_test() ->
  ?assert( sets:is_element( "x", free_vars( {fix, {var, "x"}} ) ) ).

zipwith_is_neutral_to_free_vars_test() ->
  ?assert( sets:is_element( "x", free_vars( {zipwith, ["x"], {var, "x"}} ) ) ).

true_has_no_free_vars_test() ->
  ?assertEqual( 0, sets:size( free_vars( true ) ) ).

false_has_no_free_vars_test() ->
  ?assertEqual( 0, sets:size( free_vars( false ) ) ).

cnd_gives_union_of_if_then_and_else_free_vars_test() ->
  T = {cnd, {var, "a"}, {var, "b"}, {var, "c"}},
  ?assertEqual( 3, sets:size( free_vars( T ) ) ).

str_has_no_free_vars_test() ->
  ?assertEqual( 0, sets:size( free_vars( {str, "blub"} ) ) ).

file_has_no_free_vars_test() ->
  ?assertEqual( 0, sets:size( free_vars( {file, "blub"} ) ) ).

nl_has_no_free_vars_test() ->
  ?assertEqual( 0, sets:size( free_vars( {nl, tbool} ) ) ).

cons_gives_union_of_head_and_tail_free_vars_test() ->
  T = {cons, tbool, {var, "a"}, {cons, tbool, {var, "b"}, {nl, tbool}}},
  ?assertEqual( 2, sets:size( free_vars( T ) ) ).

isnil_is_neutral_to_free_vars_test() ->
  ?assert( sets:is_element( "x", free_vars( {isnil, tbool, {var, "x"}} ) ) ).

tuple_gives_union_of_elements_free_vars_test() ->
  T = {tup, [{var, "x"}, {var, "y"}, {var, "z"}]},
  ?assertEqual( 3, sets:size( free_vars( T ) ) ).

proj_is_neutral_to_free_vars_test() ->
  T = {proj, 1, {tup, [{var, "x"}]}},
  ?assert( sets:is_element( "x", free_vars( T ) ) ).


%% Alpha Renaming

renaming_leaves_unconcerned_var_untouched_test() ->
  ?assertEqual( {var, "y"}, rename( "x", {var, "y"} ) ).

renaming_alters_concerned_var_test() ->
  T1 = {var, "x"},
  T2 = rename( "x", T1 ),
  ?assertMatch( {var, _}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_alters_native_abstraction_test() ->
  T1 = {abs_nat, #{ "x" => tbool }, {var, "y"}},
  T2 = rename( "x", T1 ),
  ?assertMatch( {abs_nat, #{}, {var, "y"}}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_alters_native_abstraction_body_test() ->
  T1 = {abs_nat, #{ "x" => tbool }, {var, "y"}},
  T2 = rename( "y", T1 ),
  ?assertMatch( {abs_nat, #{ "x" := tbool }, {var, _}}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_alters_signature_of_foreign_abstraction_test() ->
  T1 = {abs_for, #{ "x" => tbool }, tbool, bash, "blub"},
  T2 = rename( "x", T1 ),
  ?assertMatch( {abs_for, #{}, tbool, bash, "blub"}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_leaves_unconcerned_untouched_in_foreign_abstraction_test() ->
  T1 = {abs_for, #{ "x" => tbool }, tbool, bash, "blub"},
  T2 = rename( "y", T1 ),
  ?assertEqual( {abs_for, #{ "x" => tbool }, tbool, bash, "blub"}, T2 ).

renaming_is_delegated_to_left_in_app_test() ->
  T1 = {app, {var, "x"}, #{ "a" => {var, "y"} }},
  T2 = rename( "x", T1 ),
  ?assertMatch( {app, {var, _}, #{ "a" := {var, "y"} }}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_is_delegated_to_right_in_app_test() ->
  T1 = {app, {var, "x"}, #{ "a" => {var, "y"} }},
  T2 = rename( "y", T1 ),
  ?assertMatch( {app, {var, "x"}, #{ "a" := {var, _} }}, T2 ),
  ?assertNotEqual( T1, T2 ).

fix_is_neutral_to_renaming_test() ->
  T1 = {fix, {var, "x"}},
  T2 = rename( "x", T1 ),
  ?assertMatch( {fix, {var, _}}, T2 ),
  ?assertNotEqual( T1, T2 ),
  ?assertEqual( T1, rename( "a", T1 ) ).
  
renaming_alters_signature_of_zipwith_test() ->
  T1 = {zipwith, ["x"], {var, "y"}},
  T2 = rename( "x", T1 ),
  ?assertMatch( {zipwith, [_], {var, "y"}}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_alters_body_of_zipwith_test() ->
  T1 = {zipwith, ["x"], {var, "y"}},
  T2 = rename( "y", T1 ),
  ?assertMatch( {zipwith, ["x"], {var, _}}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_leaves_unconcerned_untouched_in_zipwith_test() ->
  T1 = {zipwith, ["x"], {var, "y"}},
  T2 = rename( "a", T1 ),
  ?assertEqual( T1, T2 ).

renaming_leaves_true_unaltered_test() ->
  ?assertEqual( true, rename( "x", true ) ).

renaming_leaves_false_unaltered_test() ->
  ?assertEqual( false, rename( "x", false ) ).

renaming_is_delegated_to_if_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  T2 = rename( "x", T1 ),
  ?assertMatch( {cnd, {var, _}, {var, "y"}, {var, "z"}}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_is_delegated_to_then_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  T2 = rename( "y", T1 ),
  ?assertMatch( {cnd, {var, "x"}, {var, _}, {var, "z"}}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_is_delegated_to_else_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  T2 = rename( "z", T1 ),
  ?assertMatch( {cnd, {var, "x"}, {var, "y"}, {var, _}}, T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_leaves_unconcerned_untouched_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  T2 = rename( "a", T1 ),
  ?assertEqual( {cnd, {var, "x"}, {var, "y"}, {var, "z"}}, T2 ).

renaming_leaves_str_unaltered_test() ->
  ?assertEqual( {str, "blub"}, rename( "x", {str, "blub"} ) ).

renaming_leaves_file_unaltered_test() ->
  ?assertEqual( {file, "blub"}, rename( "x", {file, "blub"} ) ).

renaming_leaves_nil_unaltered_test() ->
  ?assertEqual( {nl, tbool}, rename( "x", {nl, tbool} ) ).

renaming_is_delegated_to_head_in_cons_test() ->
  T1 = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  T2 = rename( "x", T1 ),
  ?assertMatch( {cons, tbool, {var, _}, {cons, tbool, {var, "y"}, {nl, tbool}}},
                T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_is_delegated_to_tail_in_cons_test() ->
  T1 = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  T2 = rename( "y", T1 ),
  ?assertMatch( {cons, tbool, {var, "x"}, {cons, tbool, {var, _}, {nl, tbool}}},
                T2 ),
  ?assertNotEqual( T1, T2 ).

renaming_leaves_unconcerned_untouched_in_cons_test() ->
  T1 = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  T2 = rename( "a", T1 ),
  ?assertEqual( {cons, tbool, {var, "x"}, {cons, tbool,
                                                 {var, "y"},
                                                 {nl, tbool}}},
                T2 ).

isnil_is_neutral_to_renaming_test() ->
  T1 = {isnil, tbool, {var, "x"}},
  T2 = rename( "x", T1 ),
  ?assertMatch( {isnil, tbool, {var, _}}, T2 ),
  ?assertNotEqual( T1, T2 ),
  ?assertEqual( T1, rename( "a", T1 ) ).

renaming_is_delegated_to_elements_in_tuple_test() ->
  T1 = {tup, [{var, "x"}]},
  T2 = rename( "x", T1 ),
  ?assertMatch( {tup, [{var, _}]}, T2 ),
  ?assertNotEqual( T1, T2 ),
  ?assertEqual( T1, rename( "a", T1 ) ).

proj_is_neutral_to_renaming_test() ->
  T1 = {proj, 1, {var, "x"}},
  T2 = rename( "x", T1 ),
  ?assertMatch( {proj, 1, {var, _}}, T2 ),
  ?assertNotEqual( T1, T2 ),
  ?assertEqual( T1, rename( "a", T1 ) ).

-endif.

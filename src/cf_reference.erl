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
-author( "Jorgen Brandt <brandjoe@hu-berlin.de>" ).

-export( [as/2, let_bind/4, step/1, subst/3, free_vars/1, rename/2] ).

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

-type fix()      :: {fix, Tm::tm()}.

-type zipwith()  :: {zipwith, ArgLst::[string()], Tm::tm()}.

-type cnd()      :: {cnd, IfTm::tm(), ThenTm::tm(), ElseTm::tm()}.

-type str()      :: {str, string()}.

-type file()     :: {file, string()}.

-type nl()       :: {nl, Tp::tp()}.

-type cons()     :: {cons, Tp::tp(), Head::tm(), Tail::tm()}.

-type isnil()    :: {isnil, Tp::tp(), Tm::tm()}.

-type tup()      :: {tup, [tm()]}.

-type proj()     :: {proj, I::pos_integer(), Tuple::tm()}.


%% Types

-type tp()       :: tabs_nat() | tabs_for()
                  | tbool | tstr | tfile | tlst() | ttup().

-type utp()      :: tbool | tstr | tfile | tlst() | ttup().

-type ttup()     :: {ttup, ElemLst::[tp()]}.

-type tlst()     :: {tlst, tp()}.

-type tabs_nat() :: {tabs, nat, Sign::ctx(), Tret::tp()}.

-type tabs_for() :: {tabs, for, Sign::uctx(), Tret::utp()}.

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
%% Evaluation
%%====================================================================

%% @doc Takes a single evaluation step.

-spec step( tm() ) -> tm().

step( _Tm ) -> error( nyi ).

%%====================================================================
%% Type System
%%====================================================================

%% @doc Infers the type of a term `T` by applying the inversion lemma.

-spec type_of( T::tm(), Ctx::ctx() ) -> tp().

type_of( {var, X}, Ctx ) ->

  % check if type is declared in context
  case Ctx of
    #{ X := Tp } -> Tp;
    _            -> throw( {eundef, var, basename( X )} )
  end;

type_of( {abs_nat, Sign, Body}, Ctx ) ->
  Ctx1 = maps:merge( Ctx, Sign ),
  {tabs, nat, Sign, type_of( Body, Ctx1 )};

type_of( {abs_for, Sign, RetTp, _, _}, _Ctx ) ->
  {tabs, for, Sign, RetTp};

type_of( {app, Left, Right}, Ctx ) ->

  {tabs, _, Sign, Tret} = type_of( Left, Ctx ),

  LeftNameLst = maps:keys( Sign ),
  LeftNameSet = sets:from_list( LeftNameLst ),
  RightNameSet = sets:from_list( maps:keys( Right ) ),
  UnboundSet = sets:subtract( LeftNameSet, RightNameSet ),
  UnusedSet = sets:subtract( RightNameSet, LeftNameSet ),

  F = fun( Name ) ->
        #{ Name := LeftTp } = Sign,
        #{ Name := RightTm } = Right,
        RightTp = type_of( RightTm, Ctx ),
        if
          LeftTp =/= RightTp ->
            throw( {etype_mismatch, app, {Name, LeftTp, RightTp}} );
          true -> ok
        end
      end,

  % check if all arguments on left hand side are bound in right hand side
  case sets:size( UnboundSet ) of
    0 -> 
      % check if all arguments on right hand side are used in left hand side
      case sets:size( UnusedSet ) of
        0 ->
          % check if types match
          lists:foreach( F, LeftNameLst ),
          Tret;
        _ -> throw( {earg_unused, app, sets:to_list( UnusedSet )} )
      end;
    _ -> throw( {earg_unbound, app, sets:to_list( UnboundSet )} )
  end;


type_of( {fix, T1}, Ctx ) ->

  {tabs, Tau, Sign, Tret} = type_of( T1, Ctx ),

  % TODO: check if signature corresponds to Tret
  % TODO: check if wrapper abstraction is native
  % TODO: check if target abstraction is native

  Tret;

type_of( {zipwith, ArgLst, T1}, Ctx ) ->
  
  F = fun( Arg, Tp ) ->
        case lists:member( Arg, ArgLst ) of
          true  -> {tlst, Tp};
          false -> Tp
        end
      end,

  {tabs, Tau, Sign, Tret} = type_of( T1, Ctx ),

  Sign1 = maps:map( F, Sign ),
  Tret1 = {tlst, Tret},

  % check if every arg is also an arg in T1
  ArgLst1 = maps:keys( Sign ),
  Pred = fun( Arg ) ->
           case lists:member( Arg, ArgLst1 ) of
             true  -> false;
             false -> true
           end
         end,

  case lists:filter( Pred, ArgLst ) of
    []       -> {tabs, Tau, Sign1, Tret1};
    UndefLst -> throw( {earg_undefined, zipwith, UndefLst} )
  end;

type_of( T, _ ) when is_boolean( T ) ->
  tbool;

type_of( {cnd, IfTm, ThenTm, ElseTm}, Ctx ) ->

  IfTp = type_of( IfTm, Ctx ),
  ThenTp = type_of( ThenTm, Ctx ),
  ElseTp = type_of( ElseTm, Ctx ),

  % check if IfTm is of type bool
  case IfTp of
    tbool ->
      % check if ElseTm is of correct type
      case ElseTp of
        ThenTp -> ThenTp;
        _      -> throw( {ethenelse_type, cnd, {ThenTp, ElseTp}} )
      end;
    _ -> throw( {eiftype, cnd, IfTp} )
  end;

type_of( {str, _}, _ ) ->
  tstr;

type_of( {file, _}, _ ) ->
  tfile;

type_of( {nl, Tp}, _ ) ->
  {tlst, Tp};

type_of( {cons, Tp, Hd, Tl}, Ctx ) ->

  HdTp = type_of( Hd, Ctx ),
  TlTp = type_of( Tl, Ctx ),

  % check type of head
  case HdTp of
    Tp ->
      % check type of tail
      case TlTp of
        {tlst, Tp} -> {tlst, Tp};
        _         -> throw( {etail_type, cons, {{tlst, Tp}, TlTp}} )
      end;
    _  -> throw( {ehead_type, cons, {Tp, HdTp}} )
  end;

type_of( {isnil, Tp, T1}, Ctx ) ->
  
  Tp1 = type_of( T1, Ctx ),

  % check if declared type matches list type
  case Tp1 of
    {tlst, Tp} -> tbool;
    _          -> throw( {elst_type, isnil, {{tlst, Tp}, Tp1}} )
  end;

type_of( {tup, ElemLst}, Ctx ) ->
  {ttup, [type_of( Elem, Ctx ) || Elem <- ElemLst]};

type_of( {proj, I, T1}, Ctx ) ->

  {ttup, TypeLst} = type_of( T1, Ctx ),

  % check if index out of bounds
  case I > length( TypeLst ) orelse I =< 0 of
    true  -> throw( {ebad_index, proj, I} );
    false -> lists:nth( I, TypeLst )
  end.



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

  {abs_nat, Sign2, subst( X, S, Body2 )};

subst( _, _, T={abs_for, _, _, _, _} ) ->
  T;

subst( X, S, {app, Left, Right} ) ->
  Left1 = subst( X, S, Left ),
  Right1 = maps:map( fun( _, V ) -> subst( X, S, V ) end, Right ),
  {app, Left1, Right1};

subst( X, S, {fix, T1} ) ->
  {fix, subst( X, S, T1 )};

subst( X, S, {zipwith, ArgLst, T1} ) ->
  {zipwith, ArgLst, subst( X, S, T1 )};

subst( _, _, T ) when is_boolean( T ) ->
  T;

subst( X, S, {cnd, IfTm, ThenTm, ElseTm} ) ->
  {cnd, subst( X, S, IfTm ), subst( X, S, ThenTm ), subst( X, S, ElseTm )};

subst( _, _, T={str, _} ) ->
  T;

subst( _, _, T={file, _} ) ->
  T;

subst( _, _, T={nl, _} ) ->
  T;

subst( X, S, {cons, Tp, T1, T2} ) ->
  {cons, Tp, subst( X, S, T1 ), subst( X, S, T2 )};

subst( X, S, {isnil, Tp, T1} ) ->
  {isnil, Tp, subst( X, S, T1 )};

subst( X, S, {tup, ElemLst} ) ->
  {tup, [subst( X, S, Elem ) || Elem <- ElemLst]};

subst( X, S, {proj, I, T1} ) ->
  {proj, I, subst( X, S, T1 )}.


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

free_vars( T )when is_boolean( T ) ->
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
%%      `T` replacing it with a fresh name.

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

        F( _, S, _ ) when is_boolean( S ) ->
          S;

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

  Fresh = basename( X )++fresh_name(),

  Renm( X, T, Fresh ).


%%====================================================================
%% Internal Functions
%%====================================================================

%% @doc Generates a fresh name.

-spec fresh_name() -> string().

fresh_name() ->
  N = erlang:unique_integer( [positive, monotonic] ),
  [$$|integer_to_list( N )].


%% @doc Restores the original name from a name that might have undergone alpha
%%      renaming.

-spec basename( string() ) -> string().

basename( X ) ->
  case string:chr( X, $$ ) of
    0 -> X;
    I -> lists:sublist( X, I-1 )
  end.


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


%% Substitution

substitution_leaves_unconcerned_untouched_in_var_test() ->
  T1 = {var, "x"},
  T2 = subst( "y", {var, "a"}, T1 ),
  ?assertEqual( T1, T2 ).

substitution_alters_concerned_var_test() ->
  T1 = {var, "x"},
  S = {fix, {var, "a"}},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( S, T2 ).

substitution_alters_free_var_in_native_abstraction_test() ->
  T1 = {abs_nat, #{ "y" => tbool }, {var, "x"}},
  S = {abs_nat, #{ "z" => tbool }, {app, {var, "z"}, #{ "a" => {var, "w"}}}},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {abs_nat, #{ "y" => tbool },
                          {abs_nat, #{ "z" => tbool },
                                    {app, {var, "z"},
                                          #{ "a" => {var, "w"}}}}}, T2 ).

substitution_leaves_bound_vars_unaltered_test() ->
  T1 = {abs_nat, #{ "x" => tbool }, {var, "x"}},
  S = {var, "y"},
  T2 = subst( "x", S, T1 ),
  {abs_nat, Sign, {var, X}} = T2,
  ?assertMatch( #{ X := tbool}, Sign ).

substitution_is_capture_avoiding_test() ->
  T1 = {abs_nat, #{ "z" => tbool }, {var, "x"}},
  S = {var, "z"},
  T2 = subst( "x", S, T1 ),
  {abs_nat, Sign, {var, Z2}} = T2,
  [Z1] = maps:keys( Sign ),
  ?assertNotEqual( Z1, Z2 ).

substitution_leaves_foreign_abstractions_untouched_test() ->
  T1 = {abs_for, #{ "a" => tbool }, tbool, bash, "blub"},
  S = {var, "z"},
  T2 = subst( "a", S, T1 ),
  ?assertEqual( T1, T2 ).

substitution_is_delegated_to_left_in_app_test() ->
  T1 = {app, {var, "x"}, #{ "a" => {var, "y"} }},
  S = {var, "z"},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {app, {var, "z"}, #{ "a" => {var, "y"} }}, T2 ).

substitution_is_delegated_to_right_in_app_test() ->
  T1 = {app, {var, "x"}, #{ "a" => {var, "y"} }},
  S = {var, "z"},
  T2 = subst( "y", S, T1 ),
  ?assertEqual( {app, {var, "x"}, #{ "a" => {var, "z"} }}, T2 ).

fix_is_neutral_to_substitution_test() ->
  T1 = {fix, {var, "x"}},
  S = {var, "y"},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {fix, S}, T2 ).

zipwith_is_neutral_to_substitution_test() ->
  T1 = {zipwith, ["a"], {var, "x"}},
  S = {var, "y"},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {zipwith, ["a"], S}, T2 ).

substitution_leaves_true_unaltered_test() ->
  ?assertEqual( true, subst( "x", {var, "y"}, true ) ).

substitution_leaves_false_unaltered_test() ->
  ?assertEqual( false, subst( "x", {var, "y"}, false ) ).

substitution_is_delegated_to_if_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  S = {var, "a"},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {cnd, S, {var, "y"}, {var, "z"}}, T2 ).

substitution_is_delegated_to_then_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  S = {var, "a"},
  T2 = subst( "y", S, T1 ),
  ?assertEqual( {cnd, {var, "x"}, S, {var, "z"}}, T2 ).

substitution_is_delegated_to_else_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  S = {var, "a"},
  T2 = subst( "z", S, T1 ),
  ?assertEqual( {cnd, {var, "x"}, {var, "y"}, S}, T2 ).

substitution_leaves_str_unaltered_test() ->
  ?assertEqual( {str, "blub"}, subst( "x", {var, "y"}, {str, "blub"} ) ).

substitution_leaves_file_unaltered_test() ->
  ?assertEqual( {file, "blub"}, subst( "x", {var, "y"}, {file, "blub"} ) ).

substitution_leaves_nil_unaltered_test() ->
  ?assertEqual( {nl, tbool}, subst( "x", {var, "y"}, {nl, tbool} ) ).

substitution_is_delegated_to_head_in_cons_test() ->
  T1 = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  S = {var, "z"},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {cons, tbool, S, {cons, tbool, {var, "y"}, {nl, tbool}}}, T2 ).

substitution_is_delegated_to_tail_in_cons_test() ->
  T1 = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  S = {var, "z"},
  T2 = subst( "y", S, T1 ),
  ?assertEqual( {cons, tbool, {var, "x"}, {cons, tbool, S, {nl, tbool}}}, T2 ).

isnil_is_neutral_to_substitution_test() ->
  T1 = {isnil, tbool, {var, "x"}},
  S = {var, "y"},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {isnil, tbool, S}, T2 ),
  ?assertEqual( T1, subst( "a", S, T1 ) ).

substitution_is_delegated_to_tuple_elements_test() ->
  T1 = {tup, [{var, "x"}]},
  S = {var, "y"},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {tup, [S]}, T2 ).

projection_is_neutral_to_substitution_test() ->
  T1 = {proj, 1, {var, "x"}},
  S = {var, "y"},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {proj, 1, S}, T2 ).


%% Type Inference

type_of_var_is_looked_up_in_context_test() ->
  ?assertEqual( tbool, type_of( {var, "x"}, #{ "x" => tbool } ) ).

var_not_in_ctx_untypable_test() ->
  ?assertThrow( {eundef, var, "x"}, type_of( {var, "x"}, #{} ) ).

type_of_foreign_abstraction_is_identical_to_declared_type_test() ->
  T1 = {abs_for, #{ "a" => tbool }, tbool, bash, "blub"},
  ?assertEqual( {tabs, for, #{ "a" => tbool }, tbool}, type_of( T1, #{} ) ).

type_of_native_abstraction_depends_on_sign_and_body_test() ->
  T1 = {abs_nat, #{ "a" => tbool }, {var, "x"}},
  ?assertEqual( {tabs, nat,  #{ "a" => tbool }, tstr},
                type_of( T1, #{ "x" => tstr } ) ).

type_of_app_is_return_type_of_left_test() ->
  T1 = {app, {abs_nat, #{ "a" => tbool }, {str, "blub"}}, #{ "a" => true }},
  ?assertEqual( tstr, type_of( T1, #{} ) ).

unbound_arg_is_untypable_test() ->
  Sign = #{ "a" => tbool, "b" => tbool },
  T1 = {app, {abs_nat, Sign, {str, "blub"}}, #{ "a" => true }},
  ?assertThrow( {earg_unbound, app, ["b"]}, type_of( T1, #{} ) ).

unused_arg_is_untypable_test() ->
  Sign = #{ "a" => tbool },
  T1 = {app, {abs_nat, Sign, {str, "blub"}}, #{ "a" => true, "b" => true }},
  ?assertThrow( {earg_unused, app, ["b"]}, type_of( T1, #{} ) ).

mismatching_types_app_is_untypable_test() ->
  Abs = {abs_nat, #{ "a" => tbool }, {str, "blub"}},
  T1 = {app, Abs, #{ "a" => {str, "blub"}}},
  Throw = {etype_mismatch, app, {"a", tbool, tstr}},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

type_of_fix_is_derivable_test() ->
  T1 = {fix, {abs_nat, #{ "f" => {tabs, nat, #{ "a" => tbool}, tstr} },
                       {abs_nat, #{ "a" => tbool }, {str, "blub"}}}},
  ?assertEqual( {tabs, nat, #{ "a" => tbool}, tstr}, type_of( T1, #{} ) ).

asymmetric_fix_is_untypable_test() ->
  T1 = {fix, {abs_nat, #{ "f" => {tabs, nat, #{ "a" => tbool}, tstr} },
                       {abs_nat, #{ "a" => tbool }, false}}},
  Throw = {easymmetric, fix, {{tabs, nat, #{ "a" => tbool}, tstr},
                              {tabs, nat, #{ "a" => tbool}, tbool}}},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

fix_with_nonnative_wrapper_is_untypable_test() ->
  T1 = {fix, {abs_for, #{ "f" => {tabs, nat, #{ "a" => tbool}, tstr} },
                       {tabs, nat, #{ "a" => tbool}, tstr},
                       bash,
                       "blub"}},
  Throw = {enonnative, fix, wrapper},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

fix_with_nonnative_target_is_untypable_test() ->
  T1 = {fix, {abs_nat, #{ "f" => {tabs, nat, #{ "a" => tbool}, tstr} },
                       {abs_for, #{ "a" => tbool }, tstr, bash, "blub"}}},
  Throw = {enonnative, target},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

type_of_zipwith_is_derivable_test() ->
  T12 = {abs_nat, #{ "a" => tbool, "b" => tbool }, {str, "blub"}},
  T1 = {zipwith, ["a"], T12},
  T2 = {tabs, nat, #{ "a" => {tlst, tbool}, "b" => tbool }, {tlst, tstr}},
  ?assertEqual( T2, type_of( T1, #{} ) ).

unbound_arg_in_zipwith_is_untypable_test() ->
  T12 = {abs_nat, #{ "a" => tbool, "b" => tbool }, {str, "blub"}},
  T1 = {zipwith, ["c"], T12},
  Throw = {earg_undefined, zipwith, ["c"]},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

type_of_true_is_tbool_test() ->
  ?assertEqual( tbool, type_of( true, #{} ) ).

type_of_false_is_tbool_test() ->
  ?assertEqual( tbool, type_of( false, #{} ) ).

type_of_cnd_is_then_else_type_test() ->
  T1 = {cnd, true, {str, "blub"}, {str, "bla"}},
  ?assertEqual( tstr, type_of( T1, #{} ) ).

if_term_not_tbool_is_untypable_test() ->
  T1 = {cnd, {str, "lala"}, {str, "blub"}, {str, "bla"}},
  ?assertThrow( {eiftype, cnd, tstr}, type_of( T1, #{} ) ).

then_and_else_term_type_mismatch_untypable_test() ->
  T1 = {cnd, true, {str, "blub"}, {file, "bla"}},
  ?assertThrow( {ethenelse_type, cnd, {tstr, tfile}}, type_of( T1, #{} ) ).

type_of_str_is_tstr_test() ->
  ?assertEqual( tstr, type_of( {str, "blub"}, #{} ) ).

type_of_file_is_tstr_test() ->
  ?assertEqual( tfile, type_of( {file, "blub"}, #{} ) ).

type_of_nil_is_list_test() ->
  ?assertEqual( {tlst, tstr}, type_of( {nl, tstr}, #{} ) ).

type_of_cons_is_list_test() ->
  T1 = {cons, tstr, {str, "blub"}, {nl, tstr}},
  ?assertEqual( {tlst, tstr}, type_of( T1, #{} ) ).

cons_head_type_mismatch_is_untypable_test() ->
  T1 = {cons, tstr, true, {nl, tstr}},
  ?assertThrow( {ehead_type, cons, {tstr, tbool}}, type_of( T1, #{} ) ).

cons_tail_type_mismatch_is_untypable_test() ->
  T1 = {cons, tstr, {str, "blub"}, {nl, tbool}},
  ?assertThrow( {etail_type, cons, {{tlst, tstr}, {tlst, tbool}}}, type_of( T1, #{} ) ).

type_of_isnil_is_tbool_test() ->
  ?assertEqual( tbool, type_of( {isnil, tstr, {nl, tstr}}, #{} ) ).

isnil_type_mismatch_is_untypable_test() ->
  T1 = {isnil, tstr, {nl, tbool}},
  ?assertThrow( {elst_type, isnil, {{tlst, tstr}, {tlst, tbool}}}, type_of( T1, #{} ) ).

type_of_tuple_is_tup_of_element_types_test() ->
  T1 = {tup, [true, {str, "blub"}]},
  ?assertEqual( {ttup, [tbool, tstr]}, type_of( T1, #{} ) ).

type_of_proj_is_type_of_corresponding_element_test() ->
  T1 = {proj, 2, {tup, [true, {str, "blub"}]}},
  ?assertEqual( tstr, type_of( T1, #{} ) ).

proj_index_too_large_is_untypable_test() ->
  T1 = {proj, 3, {tup, [true, {str, "blub"}]}},
  ?assertThrow( {ebad_index, proj, 3}, type_of( T1, #{} ) ).

proj_index_zero_is_untypable_test() ->
  T1 = {proj, 0, {tup, [true, {str, "blub"}]}},
  ?assertThrow( {ebad_index, proj, 0}, type_of( T1, #{} ) ).

proj_index_negative_is_untypable_test() ->
  T1 = {proj, -1, {tup, [true, {str, "blub"}]}},
  ?assertThrow( {ebad_index, proj, -1}, type_of( T1, #{} ) ).

-endif.

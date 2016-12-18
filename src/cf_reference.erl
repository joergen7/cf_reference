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

-type proj()     :: {proj, Tuple::tm(), I::pos_integer()}.


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
  

%% @doc Generates a fresh name.

-spec fresh_name() -> string().

fresh_name() ->
  N = erlang:unique_integer( [positive, monotonic] ),
  [$$|integer_to_list( N )].

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

subst( X, S, T={abs_nat, Sign, Body} ) ->
  
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

free_vars( {tup, L} ) ->
  sets:union( [free_vars( X ) || X <- L] );

free_vars( {cons, _, Head, Tail} ) ->
  sets:union( free_vars( Head ), free_vars( Tail ) );

free_vars( {var, X} ) ->
  sets:add_element( X, sets:new() );

free_vars( {abs_nat, Sign, T1} ) ->
  F = fun( N, Fv ) -> sets:del_element( N, Fv ) end,
  lists:foldl( F, free_vars( T1 ), maps:keys( Sign ) );

free_vars( {app, Left, Right} ) ->
  FvLeft = free_vars( Left ),
  FvRight = sets:union( [free_vars( X ) || X <- maps:values( Right )] ),
  sets:union( FvLeft, FvRight );

free_vars( {fix, T} ) ->
  free_vars( T ).

%% @doc consistently renames all occurrences of a given name `X` in the term
%%      `T`.

-spec rename( X::string(), T::tm() ) -> tm().

rename( X, T ) ->

  F = fun

        ren( X, {var, X}, Fresh ) ->
          {var, Fresh};

        ren( _, T={var, _}, _ ) ->
          T;

        ren( X, {app, Left, Right}, Fresh ) ->
          Left1 = ren( X, Left, Fresh ),
          Right1 = maps:map( fun( _, T ) -> ren( X, T, Fresh ) end, Right ),
          {app, Left1, Right1};

        ren( X, {abs_nat, } )


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


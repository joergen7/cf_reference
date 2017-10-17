%% -*- erlang -*-
%%
%% Cuneiform reference implementation
%%
%% Copyright 2016-2017 Jörgen Brandt
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

%% @author Jörgen Brandt <joergen.brandt@onlinehome.de>

-module( cf_reference ).

-export( [arg_ntv/3, arg_frn/2, bind/2, str/1, file/1, lambda_ntv/2,
          lambda_frn/5, app/2, fut/1, true/0, false/0, cnd/3] ).
-export( [t_arg/2, t_str/0, t_file/0, t_bool/0, t_fn/3] ).
-export( [l_bash/0, l_octave/0, l_perl/0, l_python/0, l_r/0] ).
-export( [is_value/1, type/1, type/2, step/1, evaluate/1] ).
-export( [gensym/1, rename/3, subst/3] ).


-ifdef( EQC ).
-export( [prop_progress/0, prop_preservation/0] ).
-include_lib( "eqc/include/eqc.hrl" ).
-define( MAX_DEPTH_E, 4 ).
-define( MAX_DEPTH_T, 2 ).
-endif.


-include( "cf_reference.hrl" ).


%%====================================================================
%% Expression constructors
%%====================================================================

-spec arg_ntv( InName, ExName, Type ) -> {atom(), string(), t()}
when InName :: atom(),
     ExName :: string(),
     Type   :: t().

arg_ntv( InName, ExName, Type )
when is_atom( InName ),
     is_list( ExName ) ->
  {InName, ExName, Type}.


-spec arg_frn( ExName :: string(), Type   :: t() ) -> {string(), t()}.

arg_frn( ExName, Type ) when is_list( ExName ) -> {ExName, Type}.


-spec bind( ExName, Expr ) -> {string(), e()}
when ExName :: string(),
     Expr   :: e().

bind( ExName, Expr )
when is_list( ExName ) ->
  {ExName, Expr}.


-spec str( S :: string() ) -> {str, string()}.

str( S ) when is_list( S ) -> {str, S}.


-spec file( S :: string() ) -> {file, string()}.

file( S ) when is_list( S ) -> {file, S}.


-spec lambda_ntv( ArgLst, Body ) -> {lambda, ntv, ArgLst, Body}
when ArgLst :: [{atom(), string(), t()}],
     Body   :: e().

lambda_ntv( ArgLst, Body ) when is_list( ArgLst ) ->
  {lambda, ntv, ArgLst, Body}.


-spec lambda_frn( LamName, ArgLst, RetType, Lang, BodyStr ) ->
  {lambda, frn, string(), [{string(), u()}], u(), l(), string()}
when LamName :: string(),
     ArgLst  :: [{string(), u()}],
     RetType :: u(),
     Lang    :: l(),
     BodyStr :: string().

lambda_frn( LamName, ArgLst, RetType, Lang, BodyStr )
when is_list( LamName ),
     is_list( ArgLst ),
     is_atom( RetType ),
     is_atom( Lang ),
     is_list( BodyStr ) ->
  {lambda, frn, LamName, ArgLst, RetType, Lang, BodyStr}.


-spec app( Lambda, BindLst ) -> {e(), [{string(), e()}]}
when Lambda  :: e(),
     BindLst :: [{string(), e()}].

app( Lambda, BindLst ) when is_list( BindLst ) ->
  {Lambda, BindLst}.


-spec fut( App ) -> Fut
when App :: {{lambda, frn, string(), [{atom(), string(), u()}], u(),
                      l(), string()},
             [{string(), e()}]},
     Fut :: {fut, {{lambda, frn, string(), [{atom(), string(), u()}], u(),
                            l(), string()},
                   [{string(), e()}]}}.

fut( App = {{lambda, frn, LamName, ArgLst, _RetType, Lang, BodyStr}, BindLst} )
when is_list( LamName ),
     is_list( ArgLst ),
     is_atom( Lang ),
     is_list( BodyStr ),
     is_list( BindLst ) ->
  {fut, App}.


-spec true() -> true.

true() -> true.


-spec false() -> false.

false() -> false.


-spec cnd( EIf :: e(), EThen :: e(), EElse :: e() ) -> {cnd, e(), e(), e()}.

cnd( EIf, EThen, EElse ) -> {cnd, EIf, EThen, EElse}.


%%====================================================================
%% Type constructors
%%====================================================================

-spec t_arg( ExName :: string(), Type   :: t() ) -> {string(), t()}.

t_arg( ExName, Type ) when is_list( ExName ) -> {ExName, Type}.


-spec t_str() -> 'Str'.

t_str() -> 'Str'.


-spec t_file() -> 'File'.

t_file() -> 'File'.


-spec t_bool() -> 'Bool'.

t_bool() -> 'Bool'.


-spec t_fn( Tau, TArgLst, RetType ) -> {'Fn', ntv | frn, [{string(), t()}], t()}
when Tau     :: ntv | frn,
     TArgLst :: [{string(), t()}],
     RetType :: t().

t_fn( Tau, TArgLst, RetType )
when is_atom( Tau ),
     is_list( TArgLst ) ->
  {'Fn', Tau, TArgLst, RetType}.
     



%%====================================================================
%% Language id constructors
%%====================================================================

-spec l_bash() -> 'Bash'.
l_bash() -> 'Bash'.

-spec l_octave() -> 'Octave'.
l_octave() -> 'Octave'.

-spec l_perl() -> 'Perl'.
l_perl() -> 'Perl'.

-spec l_python() -> 'Python'.
l_python() -> 'Python'.

-spec l_r() -> 'R'.
l_r() -> 'R'.


%%====================================================================
%% Predicates
%%====================================================================

-spec is_value( E :: e() ) -> boolean().

is_value( {str, _S} )                                       -> true;
is_value( {file, _S} )                                      -> true;
is_value( E ) when is_boolean( E )                          -> true;
is_value( X ) when is_atom( X )                             -> false;
is_value( {lambda, ntv, _ArgLst, _Body} )                   -> true;
is_value( {_E, BindLst} ) when is_list( BindLst )           -> false;
is_value( {lambda, frn, _, _, _, _, _} )                    -> true;
is_value( {fut, {{lambda, frn, _, _, _, _, _}, _BindLst}} ) -> false;
is_value( {cnd, _EEif, _EThen, _EElse} )                    -> false;
is_value( E ) -> error( {malformed_expr, E} ).


%%====================================================================
%% Type Checker
%%====================================================================

-spec type( E :: e() ) -> {ok, t()} | error.

type( E ) ->
  type( #{}, E ).

-spec type( Gamma :: #{ atom() => t() }, E :: e() ) -> {ok, t()} | error.

type( _Gamma, {str, _S} ) ->                                    % T-str
  {ok, t_str()};

type( _Gamma, {file, _S} ) ->                                   % T-file
  {ok, t_file()};

type( _Gamma, B ) when is_boolean( B ) ->                       % T-true/T-false
  {ok, t_bool()};

type( Gamma, X ) when is_atom( X ) ->                           % T-var
  case maps:is_key( X, Gamma ) of
  	true  -> {ok, maps:get( X, Gamma )};
  	false -> error
  end;

type( Gamma, {lambda, ntv, ArgLst, Body} ) ->                   % T-lambda-ntv

  Gamma1 = maps:merge( Gamma,
                       maps:from_list( [{X, T} || {X, _S, T} <- ArgLst] ) ),

  case type( Gamma1, Body ) of

  	error         -> error;

  	{ok, RetType} ->
      TArgLst = [{S, T} || {_X, S, T} <- ArgLst],
  	  {ok, t_fn( ntv, TArgLst, RetType )}

  end;

type( _Gamma, {lambda, frn, _, ArgLst, RetType, _, _} ) ->      % T-lambda-frn
  {ok, t_fn( frn, ArgLst, RetType )};

type( Gamma, {EFn, BindLst} ) when is_list( BindLst ) ->        % T-app

  P = fun

        ( {{ArgName, ArgType}, {ArgName, BindExpr}} ) ->
          case type( Gamma, BindExpr ) of
            error         -> false;
            {ok, ArgType} -> true;
            {ok, _}       -> false
          end;

        ( {{_, _}, {_, _}} ) ->
          false

      end,

  case type( Gamma, EFn ) of
  	error                               -> error;
    {ok, {'Fn', _Tau, ArgLst, RetType}} ->
      case length( ArgLst ) =:= length( BindLst ) of
        false -> error;
        true  ->
          case lists:all( P, lists:zip( ArgLst, BindLst ) ) of
            true  -> {ok, RetType};
            false -> error
          end
      end;
    {ok, _} -> error
  end;

type( _, {fut, {{lambda, frn, _, _, RetType, _, _}, _}} ) ->    % T-fut
  {ok, RetType};

type( Gamma, {cnd, EIf, EThen, EElse} ) ->                      % T-if
  case type( Gamma, EIf ) of
    error        -> error;
    {ok, 'Bool'} ->
      case type( Gamma, EThen ) of
        error       -> error;
        {ok, TThen} ->
          case type( Gamma, EElse ) of
            error       -> error;
            {ok, TThen} -> {ok, TThen};
            {ok, _}     -> error
          end
      end;
    {ok, _}      -> error
  end;

type( Gamma, E ) -> error( {malformed_expr, type, Gamma, E} ).

%%====================================================================
%% Substitution
%%====================================================================

-spec gensym( X :: atom() ) -> atom().

gensym( X ) when is_atom( X ) ->
  [S1|_] = string:tokens( atom_to_list( X ), "$" ),
  N = erlang:unique_integer( [positive, monotonic] ),
  S2 = [$$|integer_to_list( N )],
  list_to_atom( S1++S2 ).


-spec rename( M :: e(), X :: atom(), Y :: atom() ) -> e().

rename( {str, S}, _X, _Y )               -> {str, S};
rename( {file, S}, _X, _Y )              -> {file, S};
rename( M, _X, _Y ) when is_boolean( M ) -> M;
rename( X, X, Y ) when is_atom( X )      -> Y;
rename( X, _Y, _Z ) when is_atom( X )    -> X;

rename( {lambda, ntv, ArgLst, Body}, X, Y ) ->

  F = fun
        ( {X1, S, T} ) when X1 =:= X -> {Y, S, T};
        ( Arg )                      -> Arg
      end,

  {lambda, ntv, [F( Arg ) || Arg <- ArgLst], rename( Body, X, Y )};

rename( M = {lambda, frn, _, _, _, _, _}, _X, _Y ) -> M;

rename( {Fn, BindLst}, X, Y ) when is_list( BindLst ) ->
  BindLst1 = [{S, rename( E, X, Y )} || {S, E} <- BindLst],
  {rename( Fn, X, Y ), BindLst1};

rename( {fut, E}, _X, _Y ) -> {fut, E};

rename( {cnd, EIf, EThen, EElse}, X, Y ) ->
  {cnd, rename( EIf, X, Y), rename( EThen, X, Y ), rename( EElse, X, Y )};

rename( M, X, Y ) -> error( {malformed_expr, rename, M, X, Y} ).


-spec subst( M :: e(), X :: atom(), N :: e() ) -> e().

subst( {str, S}, _X, _N )                    -> {str, S};
subst( {file, S}, _X, _N )                   -> {file, S};
subst( M, _X, _N ) when is_boolean( M )      -> M;
subst( X, X, N ) when is_atom( X )           -> N;
subst( X, _Y, _N ) when is_atom( X )         -> X;

subst( {F, BindLst}, X, N ) when is_list( BindLst ) ->
  {subst( F, X, N ), [{S, subst( A, X, N )} || {S, A} <- BindLst]};

subst( Lambda = {lambda, ntv, ArgLst, Body}, X, N ) ->

  F = fun( {AX, AS, AT}, {lambda, ntv, AArgLst, ABody} ) ->
        AX1 = gensym( AX ),
        ABody1 = rename( ABody, AX, AX1 ),
        {lambda, ntv, [{AX1, AS, AT}|AArgLst], ABody1}
      end,

  InNameLst = [Y || {Y, _S, _T} <- ArgLst],

  case lists:member( X, InNameLst ) of
    true  -> Lambda;
    false ->
      
      Lambda1 = lists:foldr( F, {lambda, ntv, [], Body}, ArgLst ),
      {lambda, ntv, ArgLst1, Body1} = Lambda1,

      {lambda, ntv, ArgLst1, subst( Body1, X, N )}
  end;

subst( Lambda = {lambda, frn, _, _, _, _, _}, _X, _N ) ->
  Lambda;

subst( {fut, E}, _X, _N ) ->
  {fut, E};

subst( {cnd, EIf, EThen, EElse}, X, N ) ->
  {cnd, subst( EIf, X, N ), subst( EThen, X, N ), subst( EElse, X, N )};

subst( M, X, N ) -> error( {malformed_expr, subst, M, X, N} ).


%%====================================================================
%% Evaluation
%%====================================================================

-spec try_step( E :: e() ) -> norule.


%% no rule applies

try_step( {str, _S} )                     -> norule;
try_step( {file, _S} )                    -> norule;
try_step( {lambda, ntv, _ArgLst, _Body} ) -> norule;
try_step( {fut, _E} )                     -> norule;
try_step( true )                          -> norule;
try_step( false )                         -> norule;
try_step( {lambda, frn, _, _, _, _, _} )  -> norule;

%% notion of reduction

try_step( {{lambda, ntv, [], E}, []} ) ->                       % E-beta-base
  throw( E );

try_step( {{lambda, ntv, [{X, _S, _T}|ArgLst], Body},           % E-beta
           [{_S, E}|BindLst]} ) ->
  throw( {{lambda, ntv, ArgLst, subst( Body, X, E )}, BindLst} );

try_step(  App = {{lambda, frn, _, _, _, _, _}, _BindLst} ) ->  % E-sigma
  throw( fut( App ) );


%% congruence rules

try_step( {F, BindLst} ) ->
  {ok, F1} = step( F ),
  throw( {F1, BindLst} );


%% catch-all

try_step( E ) -> error( {undefined_behavior, E} ).


-spec step( E :: e() ) -> {ok, e()} | norule.

step( E ) ->

  try
    try_step( E )
  catch
    throw : E1 -> {ok, E1}
  end.


-spec evaluate( E :: e() ) -> e().

evaluate( E ) ->
  case step( E ) of
    norule   -> E;
    {ok, E1} -> evaluate( E1 )
  end.



-ifdef( EQC ).


%%====================================================================
%% EQC generators
%%====================================================================

%% gen_t

gen_sign( _Tau, 0, _N, _NameLst ) ->
  [];

gen_sign( ntv, A, N, NameLst ) when A > 0 ->
  ?LET( T, gen_t( N ),
  ?LET( Name, elements( NameLst ),
    [{Name, T}|gen_sign( ntv, A-1, N, NameLst--[Name] )] ) );

gen_sign( frn, A, N, NameLst ) when A > 0 ->
  ?LET( U, gen_u(),
  ?LET( Name, elements( NameLst ),
    [{Name, U}|gen_sign( frn, A-1, N, NameLst--[Name] )] ) ).

gen_t_str() -> ?LAZY( t_str() ).
gen_t_file() -> ?LAZY( t_file() ).
gen_t_bool() -> ?LAZY( t_bool() ).

gen_t_fn( ntv, A, N ) ->
  ?LAZY(
    ?LET( Sign, gen_sign( ntv, A, N-1, ["a", "b", "c", "d"] ),
    ?LET( RetType, gen_t( N-1 ),
      t_fn( ntv, Sign, RetType ) ) ) );

gen_t_fn( frn, A, N ) ->
  ?LAZY(
    ?LET( Sign, gen_sign( frn, A, N-1, ["a", "b", "c", "d"] ),
    ?LET( RetType, gen_u(),
      t_fn( ntv, Sign, RetType ) ) ) ).


gen_t() ->
  gen_t( ?MAX_DEPTH_T ).

gen_t( 0 ) ->
  oneof( [gen_t_str(), gen_t_file(), gen_t_bool()] );

gen_t( N ) when N > 0 ->
  ?LET( A, choose( 0, 4 ),
  ?LET( Tau, elements( [ntv, frn] ),
    oneof( [gen_t_str(), gen_t_file(), gen_t_bool(),
            gen_t_fn( Tau, A, N )] ) ) ).

gen_u() ->
  oneof( [gen_t_str(), gen_t_file(), gen_t_bool()] ).


%% gen_e

gen_typable_value( _N, _Gamma, 'Str' ) ->
  ?LAZY(
    ?LET( S, elements( ["a", "b", "c", "d"] ),
      str( S ) ) );

gen_typable_value( _N, _Gamma, 'File' ) ->
  ?LAZY(
    ?LET( S, elements( ["a", "b", "c", "d"] ),
      file( S ) ) );

gen_typable_value( _N, _Gamma, 'Bool' ) ->
  ?LAZY( elements( [true, false] ) );

gen_typable_value( N, Gamma, {'Fn', ntv, ArgLst, RetType} ) ->
  ?LAZY(
    ?LET( Body,
          gen_typable_expr(
            N,
            maps:merge( Gamma,
                        maps:from_list(
                          [{list_to_atom( S ), T} || {S, T} <- ArgLst] ) ),
            RetType ),
    lambda_ntv( [{list_to_atom( S ), S, T} || {S, T} <- ArgLst], Body ) ) );


gen_typable_value( _N, _Gamma, {'Fn', frn, ArgLst, RetType} ) ->
  ?LAZY(
    ?LET( Name, elements( ["f1", "f2", "f3", "f4"] ),
    ?LET( Lang, elements( [l_bash(),
                           l_octave(),
                           l_perl(),
                           l_python(),
                           l_r()] ),
      lambda_frn( Name, ArgLst, RetType, Lang, "..." ) ) ) ).

gen_typable_app( N, Gamma, RetType ) ->
  ?LAZY(
    ?LET( Tau, if is_atom( RetType ) -> elements( [ntv, frn] ); true -> ntv end,
    ?LET( A, choose( 0, 4 ),
    ?LET( Sign, gen_sign( ntv, A, ?MAX_DEPTH_T, ["a", "b", "c", "d"] ),
    ?LET( F, gen_typable_expr( N-1, Gamma, t_fn( Tau, Sign, RetType ) ),
    ?LET( BindLst, [{S, gen_typable_expr( N-1, Gamma, T )} || {S, T} <- Sign],
      app( F, BindLst ) ) ) ) ) ) ).

gen_typable_expr( 0, Gamma, T ) ->
  case var_lst( Gamma, T ) of
    [] ->
      gen_typable_value( 0, Gamma, T );
    VarLst ->
      oneof( [elements( VarLst ),
              gen_typable_value( 0, Gamma, T )] )
  end;


gen_typable_expr( N, Gamma, T ) when N > 0 ->
  case var_lst( Gamma, T ) of
    [] ->
      oneof( [gen_typable_value( N, Gamma, T ),
              gen_typable_app( N, Gamma, T )] );
    VarLst ->
      oneof( [elements( VarLst ),
              gen_typable_value( N, Gamma, T ),
              gen_typable_app( N, Gamma, T )] )
  end.


gen_nonvalue_typable_expr() ->
  ?LET( T, gen_t(),
    gen_typable_app( ?MAX_DEPTH_E, #{}, T ) ).


var_lst( Gamma, T ) ->

  F = fun
        ( _, CurT ) when CurT =:= T -> true;
        ( _, _ )                    -> false
      end,

  maps:keys( maps:filter( F, Gamma ) ).



%%====================================================================
%% EQC properties
%%====================================================================

%% Progress

prop_progress() ->
  ?FORALL( E, gen_nonvalue_typable_expr(),
    step( E ) =/= norule ).

%% Preservation

prop_preservation() ->
  ?FORALL( E, gen_nonvalue_typable_expr(),
    ?LET( {ok, E1}, step( E ),
      type( E ) =:= type( E1 ) ) ).

-endif.
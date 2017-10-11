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
-export( [is_value/1, type/2, step/1] ).

-ifdef( TEST ).
-include_lib( "eunit/include/eunit.hrl" ).
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
  {lambda, frn, string(), [{atom(), string(), u()}], t(), l(), string()}
when LamName :: string(),
     ArgLst  :: [{atom(), string(), u()}],
     RetType :: t(),
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
      end
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

type( _Gamma, E ) ->
  error( {malformed_expr, E} ).


%%====================================================================
%% Evaluation
%%====================================================================

-spec try_step( E :: e() ) -> norule.

try_step( {str, _S} ) -> norule;

try_step( {file, _S} ) -> norule;

try_step( {lambda, ntv, _ArgLst, _Body} ) -> norule;

try_step( {{lambda, ntv, [], E}, []} ) ->                       % E-beta-base
  throw( E );

try_step( _E ) -> error( undefined_behavior ).


-spec step( E :: e() ) -> {ok, e()} | norule.

step( E ) ->

  try
    try_step( E )
  catch
    throw : E1 -> {ok, E1}
  end.
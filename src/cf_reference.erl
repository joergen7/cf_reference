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

-export( [str/1, file/1, arg/3, lambda_ntv/2] ).
-export( [is_value/1] ).

-ifdef( TEST ).
-include_lib( "eunit/include/eunit.hrl" ).
-endif.

-include( "cf_reference.hrl" ).


%%====================================================================
%% Term constructors
%%====================================================================

-spec str( S :: string() ) -> {str, string()}.

str( S ) when is_list( S ) -> {str, S}.

-spec file( S :: string() ) -> {file, string()}.

file( S ) when is_list( S ) -> {file, S}.

-spec arg( InName, ExName, Type ) -> {atom(), string(), tp()}
when InName :: atom(),
     ExName :: string(),
     Type   :: tp().

arg( InName, ExName, Type )
when is_atom( InName ),
     is_list( ExName ),
     is_atom( Type ) ->
  {InName, ExName, Type}.

-spec lambda_ntv( ArgLst, Body ) -> {lambda, ntv, ArgLst, Body}
when ArgLst :: [arg()],
     Body   :: e().

lambda_ntv( ArgLst, Body ) when is_list( ArgLst ) ->
  {lambda, ntv, ArgLst, Body}.




%%====================================================================
%% Predicates
%%====================================================================

-spec is_value( E :: e() ) -> boolean().

is_value( {str, _S} )                     -> true;
is_value( {file, _S} )                    -> true;
is_value( {lambda, ntv, _ArgLst, _Body} ) -> true;
is_value( _E )                            -> error( malformed_expr ).




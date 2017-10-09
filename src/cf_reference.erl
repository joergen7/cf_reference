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

-export( [str/1, file/1] ).
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

%%====================================================================
%% Predicates
%%====================================================================

-spec is_value( E :: e() ) -> boolean().

is_value( {str, _S} )  -> true;
is_value( {file, _S} ) -> true;
is_value( _E )         -> false.




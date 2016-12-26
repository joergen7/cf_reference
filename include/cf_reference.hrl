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

%%====================================================================
%% Abstract Syntax
%%====================================================================

%% Terms

-type tm()       :: var() | abs_nat() | abs_for() | app()
                  | fix() | zipwith()
                  | boolean() | cnd()
                  | str() | file()
                  | nl() | cons() | isnil()
                  | tup() | proj()
                  | fut().

-type var()      :: {var, Name::string()}.

-type abs_nat()  :: {abs_nat, Sign::ctx(), Body::tm()}.

-type abs_for()  :: {abs_for, Sign::uctx(), RetTp::utp(), Lang::lang(),
                             Script::binary()}.

-type app()      :: {app, Left::tm(), Right:: arg_map()}.

-type fix()      :: {fix, Tm::tm()}.

-type zipwith()  :: {zipwith, Tret::tp(), ArgLst::[string()], Tm::tm()}.

-type cnd()      :: {cnd, IfTm::tm(), ThenTm::tm(), ElseTm::tm()}.

-type str()      :: {str, string()}.

-type file()     :: {file, string()}.

-type nl()       :: {nl, Tp::tp()}.

-type cons()     :: {cons, Tp::tp(), Head::tm(), Tail::tm()}.

-type isnil()    :: {isnil, Tp::tp(), Tm::tm()}.

-type tup()      :: {tup, [tm()]}.

-type proj()     :: {proj, I::pos_integer(), Tuple::tm()}.

-type fut()      :: {fut, Tp::utp(), K::pos_integer()}.


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
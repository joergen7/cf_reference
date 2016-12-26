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

-export( [lst/2, str/1, app/2, var/1, cnd/3, isnil/2, not_isnil/2, abs_nat/2,
          abs_for/4, file/1, nl/1, true/0, false/0, tup/1, fut/2, proj/2,
          fix/1, zipwith/3] ).
-export( [tabs_nat/2, tabs_for/2, tlst/1, tstr/0, tbool/0, tfile/0, ttup/1] ).
-export( [as/2, let_bind/4, select/3] ).
-export( [is_value/1, type_of/2, eval/2] ).

-include( "cf_reference.hrl" ).

-ifdef( TEST ).
-include_lib( "eunit/include/eunit.hrl" ).
-endif.

%%====================================================================
%% Constructors
%%====================================================================

%% Terms

lst( Tp, [] )                       -> nl( Tp );
lst( Tp, [H|T] )                    -> {cons, Tp, H, lst( Tp, T )}.
nl( Tp )                            -> {nl, Tp}.
str( S )                            -> {str, S}.
app( Left, Right )                  -> {app, Left, Right}.
var( X )                            -> {var, X}.
cnd( If, Then, Else )               -> {cnd, If, Then, Else}.
isnil( Tp, Tm )                     -> {isnil, Tp, Tm}.
not_isnil( Tp, Lst )                -> cnd( isnil( Tp, Lst ), false, true ).
abs_nat( Sign, Body )               -> {abs_nat, Sign, Body}.
abs_for( Sign, Tret, Lang, Script ) -> {abs_for, Sign, Tret, Lang, Script}.
file( S )                           -> {file, S}.
true()                              -> true.
false()                             -> false.
tup( TmLst )                        -> {tup, TmLst}.
fut( Tp, N )                        -> {fut, Tp, N}.
proj( I, Tm )                       -> {proj, I, Tm}.
fix( Tm )                           -> {fix, Tm}.
zipwith( Tret, ArgLst, Tm )         -> {zipwith, Tret, ArgLst, Tm}.

%% Types

tabs_nat( Sign, Tret ) -> {tabs, nat, Sign, Tret}.
tabs_for( Sign, Tret ) -> {tabs, for, Sign, Tret}.
tlst( T )              -> {tlst, T}.
tstr()                 -> tstr.
tbool()                -> tbool.
tfile()                -> tfile.
ttup( TpLst )          -> {ttup, TpLst}.

%% Languages

bash() -> bash.


%%====================================================================
%% Derived Forms
%%====================================================================

%% @doc Ascription as derived form.

-spec as( Term::tm(), Type::tp() ) -> tm().

as( Tm, Tp ) ->
  X = fresh_name(),
  {app, {abs_nat, #{ X => Tp }, {var, X}}, #{ X => Tm }}.


%% @doc Let bindings as derived form.

-spec let_bind( X::string(), Tp::tp(), S::tm(), Tm::tm() ) -> tm().

let_bind( X, Tp, S, Tm ) ->
  {app, {abs_nat, #{ X => Tp }, Tm}, #{ X => S }}.


%% @doc Selects the `I` th output channel from a list `TupLst` of result tuples
%%      of type `TupTp`.

-spec select( TupTp, I, TupLst ) -> tm()
when TupTp  :: ttup(),
     I      :: pos_integer(),
     TupLst :: cons().

select( TupTp={ttup, TpLst}, I, TupLst ) ->
  X = fresh_name(),
  Abs = abs_nat( #{ X => TupTp }, proj( I, var( X ) ) ),
  Tp = lists:nth( I, TpLst ),
  {app, {zipwith, Tp, [X], Abs}, #{ X => TupLst }}.
  

%%====================================================================
%% Evaluation
%%====================================================================

%% @doc Repeatedly applies the step function to `Tm` to obtain an expression
%%      that cannot be further reduced.

-spec eval( Tm::tm(), Mu::fun( ( app() ) -> fut() ) ) -> tm().

eval( Tm, Mu ) ->
  try step( Tm, Mu ) of
    Tm1 -> eval( Tm1, Mu )
  catch
    throw:enorule -> Tm
  end.

%% @doc Takes a single evaluation step, applying any applicable rule except the
%%      foreign function call rule. No special error checking is performed since
%%      terms are expected to be well-formed and well-typable. If no evaluation
%%      rules apply, a corresponding exception `enorule` of type `throw` is
%%      generated.

-spec step( tm(), fun( ( app() ) -> fut() ) ) -> tm().

step( {var, _}, _ ) ->
  throw( enorule );

step( {abs_nat, _, _}, _ ) ->
  throw( enorule );

step( {abs_for, _, _, _, _}, _ ) ->
  throw( enorule );

step( T={app, Left, Right}, Mu ) ->

  try step( Left, Mu ) of
    Left1 -> {app, Left1, Right}                                                % (9)
  catch
    throw:enorule ->
      case Left of

        {abs_nat, Sign, T12} ->
          case maps:size( Sign ) of
            0 -> T12;                                                           % (11)
            _ ->
              try step_map( maps:keys( Right ), Right, Mu ) of
                Right1 -> {app, Left, Right1}                                   % (10)
              catch
                throw:enorule ->
                  [X|_] = maps:keys( Sign ),
                  #{ X := T21 } = Right,
                  Right2 = maps:remove( X, Right ),
                  Sign2 = maps:remove( X, Sign ),
                  {app, {abs_nat, Sign2, subst( X, T21, T12 )}, Right2}         % (12)
              end
          end;

        {abs_for, _, _, _, _} ->
          try step_map( maps:keys( Right ), Right, Mu ) of
            Right1 -> {app, Left, Right1}                                       % (10)
          catch
            throw:enorule ->
              case lists:all( fun is_value/1, maps:values( Right ) ) of
                true  -> Mu( T );                                               % (13)
                false -> throw( enorule )
              end
          end;

        {zipwith, Tobj, NameLst, T12} ->
          IsNil = fun
                    IsNil( [], _ ) ->
                      false;
                    IsNil( [H|Tail], R ) ->
                      #{ H := V } = R,
                      case V of
                        {nl, _} -> true;
                        _       -> IsNil( Tail, R )
                      end
                  end,
          F = fun( X, Tr ) ->
                case lists:member( X, NameLst ) of
                  true  ->
                    {cons, _, Chd, _} = Tr,
                    Chd;
                  false -> Tr
                end
              end,
          G = fun( X, Tr ) ->
                case lists:member( X, NameLst ) of
                  true  ->
                    {cons, _, _, Ctl} = Tr,
                    Ctl;
                  false -> Tr
                end
              end,
          case IsNil( NameLst, Right ) of
            true  -> {nl, Tobj};
            false ->
              HdRight = maps:map( F, Right ),
              TlRight = maps:map( G, Right ),
              Hd = {app, T12, HdRight},
              Tl = {app, {zipwith, Tobj, NameLst, T12}, TlRight},
              {cons, Tobj, Hd, Tl}
          end
          
      end
  end;

step( T={fix, {abs_nat, Sign, Body}}, _ ) ->
  [X] = maps:keys( Sign ),
  subst( X, T, Body );

step( {fix, T1}, Mu ) ->
  {fix, step( T1, Mu )};

step( {zipwith, _, _, _}, _ ) ->
  throw( enorule );

step( {cnd, true, ThenTm, _ElseTm}, _ ) ->
  ThenTm;

step( {cnd, false, _ThenTm, ElseTm}, _ ) ->
  ElseTm;

step( {cnd, IfTm, ThenTm, ElseTm}, Mu ) ->
  {cnd, step( IfTm, Mu ), ThenTm, ElseTm};

step( {str, _}, _ ) ->
  throw( enorule );

step( {file, _}, _ ) ->
  throw( enorule );

step( {nl, _}, _ ) ->
  throw( enorule );

step( {cons, Tp, T1, T2}, Mu ) ->
  try step( T1, Mu ) of
    T11 -> {cons, Tp, T11, T2}
  catch
    throw:enorule -> {cons, Tp, T1, step( T2, Mu )}
  end;

step( {isnil, _, {nl, _}}, _ ) ->
  true;

step( {isnil, _, {cons, _, _, _}}, _ ) ->
  false;

step( {isnil, Tp, Tm}, Mu ) ->
  {isnil, Tp, step( Tm, Mu )};

step( {proj, I, {tup, ElemLst}}, _ ) ->
  lists:nth( I, ElemLst );

step( {tup, ElemLst}, Mu ) ->
  {tup, step_lst( ElemLst, Mu )};

step( {fut, _, _}, _ ) ->
  throw( enorule ).


%% @doc Tries to apply the step function to all map keys in the given list and
%%      returns an updated map if the step function is applicable. Otherwise
%%      `enorule` is thrown.

-spec step_map( ArgLst, ArgMap, Mu ) -> #{ string() => tm() }
when ArgLst :: [string()],
     ArgMap :: #{ string() => tm() },
     Mu     :: fun( ( app() ) -> fut() ).

step_map( [], _, _ ) ->
  throw( enorule );

step_map( [Hd|Tl], Map, Mu ) ->
  #{ Hd := Tm0 } = Map,
  try step( Tm0, Mu ) of
    Tm1 -> Map#{ Hd := Tm1 }
  catch
    throw:enorule -> step_map( Tl, Map, Mu )
  end.


%% @doc Tries to apply the step function to all elements in the given list and
%%      returns an updated list if the step function was applicable. Otherwise
%%      `enorule` is thrown.

-spec step_lst( TmLst, Mu ) -> [tm()]
when TmLst :: [tm()],
     Mu    :: fun( ( app() ) -> fut() ).

step_lst( [], _ ) ->
  throw( enorule );

step_lst( [Hd|Tl], Mu ) ->
  try step( Hd, Mu ) of
    Hd1 -> [Hd1|Tl]
  catch
    throw:enorule -> [Hd|step_lst( Tl, Mu )]
  end.


%% @doc Tests whether a given term is a value of a ground type.

-spec is_value( tm() ) -> boolean().

is_value( {abs_nat, _, _} )        -> true;
is_value( {abs_for, _, _, _, _} )  -> true;
is_value( T ) when is_boolean( T ) -> true;
is_value( {str, _} )               -> true;
is_value( {file, _} )              -> true;
is_value( {nl, _} )                -> true;
is_value( {cons, _, Hd, Tl} )      -> is_value( Hd ) andalso is_value( Tl );
is_value( {tup, TmLst} )           -> lists:all( fun is_value/1, TmLst );
is_value( {zipwith, _, _, _} )     -> true;
is_value( _ )                      -> false.


%%====================================================================
%% Type System
%%====================================================================

%% @doc Infers the type of a term `T` by applying the inversion lemma. If a term
%%      is untypable, an exception of type `throw` is generated.

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

  {tabs, Tau, Sign, Tret} = type_of( Left, Ctx ),

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

  G = fun( Name ) ->
        #{ Name := Tp } = Sign,
        case Tp of
          {tabs, _, _, _} ->
            throw( {earg_type, app, {Name, Tp}} );
          _ -> ok
        end
      end,

  % if foreign, check if arguments are of ground types
  case Tau of
    for -> lists:foreach( G, LeftNameLst );
    nat -> ok
  end,

  % check if all arguments on left hand side are bound in right hand side
  case sets:size( UnboundSet ) > 0 of
    true  -> throw( {earg_unbound, app, sets:to_list( UnboundSet )} );
    false -> ok
  end,

  % check if all arguments on right hand side are used in left hand side
  case sets:size( UnusedSet ) > 0 of
    true  -> throw( {earg_unused, app, sets:to_list( UnusedSet )} );
    false -> ok
  end,

  % check if types match
  lists:foreach( F, LeftNameLst ),

  Tret;




type_of( {fix, T1}, Ctx ) ->

  {tabs, Tau, Sign, Tret} = type_of( T1, Ctx ),

  % check if abstraction is native
  case Tau of
    for -> throw( {eforeign, fix, for} );
    nat ->
      % check if signature is singular
      case maps:keys( Sign ) of
        [X]     ->
          % check if signature corresponds to Tret
          case Sign of
            #{ X := Tret } -> Tret;
            #{ X := Tp }   -> throw( {easymmetric, fix, {Tp, Tret}} )
          end;
        NameLst -> throw( {enonsingular, fix, NameLst} )
      end
  end;

type_of( {zipwith, _, [], _}, _ ) ->
  throw( {ebad_namelst, zipwith, empty_namelst} );

type_of( {zipwith, DeclaredTp, ArgLst, T1}, Ctx ) ->
  
  F = fun( Arg, Tp ) ->
        case lists:member( Arg, ArgLst ) of
          true  -> {tlst, Tp};
          false -> Tp
        end
      end,

  {tabs, Tau, Sign, Tret} = type_of( T1, Ctx ),

  Sign1 = maps:map( F, Sign ),
  Tret1 = {tlst, Tret},

  ArgLst1 = maps:keys( Sign ),
  Pred = fun( Arg ) ->
           case lists:member( Arg, ArgLst1 ) of
             true  -> false;
             false -> true
           end
         end,

  % check if abtraction return type matches declared type
  case Tret of
    DeclaredTp ->
      % check if every arg is also an arg in T1
      case lists:filter( Pred, ArgLst ) of
        []       -> {tabs, Tau, Sign1, Tret1};
        UndefLst -> throw( {earg_undefined, zipwith, UndefLst} )
      end;
    _ -> throw( {ereturn_type, zipwith, {DeclaredTp, Tret}} )
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
  end;

type_of( {fut, Tp, _}, _ ) ->
  Tp.



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

subst( X, S, {zipwith, Tp, ArgLst, T1} ) ->
  {zipwith, Tp, ArgLst, subst( X, S, T1 )};

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
  {proj, I, subst( X, S, T1 )};

subst( _, _, T={fut, _, _} ) ->
  T.


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

free_vars( {zipwith, _, _, T} ) ->
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
  free_vars( T );

free_vars( {fut, _, _} ) ->
  sets:new().


%% @doc Consistently renames all occurrences of a given name `X` in the term `T`
%%      replacing it with a fresh name.

-spec rename( X::string(), T::tm() ) -> tm().

rename( X, T ) ->
  Fresh = basename( X )++fresh_name(),
  rename_term( X, T, Fresh ).


%% @doc Consistently renames all occurrences of a given name `X` in the term `T`
%%      replacing it with the given fresh name `Fresh`.

-spec rename_term( X::string(), T::tm(), Fresh::string() ) -> tm().

rename_term( X, {var, X}, Fresh ) ->
  {var, Fresh};

rename_term( _, T={var, _}, _ ) ->
  T;

rename_term( X, {abs_nat, Sign, Body}, Fresh ) ->
  Sign1 = rename_sign( X, Sign, Fresh ),
  Body1 = rename_term( X, Body, Fresh ),
  {abs_nat, Sign1, Body1};

rename_term( X, {abs_for, Sign, RetTp, Lang, Script}, Fresh ) ->
  Sign1 = rename_sign( X, Sign, Fresh ),
  {abs_for, Sign1, RetTp, Lang, Script};

rename_term( X, {app, Left, Right}, Fresh ) ->

  F = fun( _, T ) ->
        rename_term( X, T, Fresh )
      end,

  Right1 = maps:map( F, Right ),

  Right2 = case maps:is_key( X, Right1 ) of
             false -> Right1;
             true  ->
               #{ X := T } = Right1,
               maps:put( Fresh, T, maps:remove( X, Right1 ) )
           end,

  Left1 = rename_term( X, Left, Fresh ),

  {app, Left1, Right2};

rename_term( X, {fix, S}, Fresh ) ->
  {fix, rename_term( X, S, Fresh )};

rename_term( X, {zipwith, Tp, ArgLst, S}, Fresh ) ->
  ArgLst1 = case lists:member( X, ArgLst ) of
              false -> ArgLst;
              true  -> [Fresh|lists:delete( X, ArgLst )]
            end,
  {zipwith, rename_type( X, Tp, Fresh ), ArgLst1, rename_term( X, S, Fresh )};

rename_term( _, S, _ ) when is_boolean( S ) ->
  S;

rename_term( Y, {cnd, If, Then, Else}, Fresh ) ->
  {cnd, rename_term( Y, If, Fresh ),
        rename_term( Y, Then, Fresh ),
        rename_term( Y, Else, Fresh )};

rename_term( _, S={str, _}, _ ) ->
  S;

rename_term( _, S={file, _}, _ ) ->
  S;

rename_term( Y, {nl, Tp}, Fresh ) ->
  {nl, rename_type( Y, Tp, Fresh )};

rename_term( Y, {cons, Tp, S1, S2}, Fresh ) ->
  {cons, rename_type( Y, Tp, Fresh ),
         rename_term( Y, S1, Fresh ),
         rename_term( Y, S2, Fresh )};

rename_term( Y, {isnil, Tp, S}, Fresh ) ->
  {isnil, rename_type( Y, Tp, Fresh ), rename_term( Y, S, Fresh )};

rename_term( Y, {tup, ElemLst}, Fresh ) ->
  {tup, [rename_term( Y, Elem, Fresh ) || Elem <- ElemLst]};

rename_term( Y, {proj, I, S}, Fresh ) ->
  {proj, I, rename_term( Y, S, Fresh )};

rename_term( _, S={fut, _, _}, _ ) ->
  S.


%% @doc Consistently renames all occurrences of a given name `X` in the type
%%      `Tp` replacing it with the name `Fresh`.

-spec rename_type( X::string(), Tp::tp(), Fresh::string() ) -> tp().

rename_type( X, {tabs, nat, Sign, Tret}, Fresh ) ->
  Sign1 = rename_sign( X, Sign, Fresh ),
  Tret1 = rename_type( X, Tret, Fresh ),
  {tabs, nat, Sign1, Tret1};

rename_type( _, tbool, _ ) ->
  tbool;

rename_type( _, tstr, _ ) ->
  tstr;

rename_type( _, tfile, _ ) ->
  tfile;

rename_type( X, {tlst, Tp1}, Fresh ) ->
  {tlst, rename_type( X, Tp1, Fresh )};

rename_type( X, {ttup, TpLst}, Fresh ) ->
  {ttup, [rename_type( X, T, Fresh ) || T <- TpLst]}.


%% @doc Consistently renames all occurrences of the name `X` in the signature
%%      `Sign` replacing it with the fresh name `Fresh`.

-spec rename_sign( X::string(), Sign::ctx(), Fresh::string() ) -> ctx().

rename_sign( X, Sign, Fresh ) ->

  F = fun( _, Tp ) ->
        rename_type( X, Tp, Fresh )
      end,

  Sign1 = maps:map( F, Sign ),

  case maps:is_key( X, Sign1 ) of
    false -> Sign1;
    true  ->
      #{ X := Tp } = Sign1,
      maps:put( Fresh, Tp, maps:remove( X, Sign1 ) )
  end.

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

-define( MU, fun( {app, {abs_for, _, Tret, _, _}, _} ) -> {fut, Tret, 23} end ).

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
  T1 = {zipwith, tbool, ["x"], {var, "x"}},
  ?assert( sets:is_element( "x", free_vars( T1 ) ) ).

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

futures_do_not_contain_free_vars_test() ->
  ?assertEqual( 0, sets:size( free_vars( {fut, tbool, 12} ) ) ).


%% Alpha Renaming

renaming_leaves_unconcerned_var_untouched_test() ->
  ?assertEqual( {var, "y"}, rename_term( "x", {var, "y"}, "x$1" ) ).

renaming_alters_concerned_var_test() ->
  T1 = {var, "x"},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {var, "x$1"}, T2 ).

renaming_alters_name_in_signature_of_native_abstraction_test() ->
  T1 = {abs_nat, #{ "x" => tbool }, {var, "y"}},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {abs_nat, #{ "x$1" => tbool }, {var, "y"}}, T2 ).

renaming_alters_type_in_signature_of_native_abstraction_test() ->
  T1 = {abs_nat, #{ "x" => {tabs, nat, #{ "a" => tstr }, tbool} }, {var, "y"}},
  T2 = rename_term( "a", T1, "a$1" ),
  Texp = {abs_nat, #{ "x" => {tabs, nat, #{ "a$1" => tstr }, tbool} },
                   {var, "y"}},
  ?assertEqual( Texp, T2 ).

renaming_alters_body_in_native_abstraction_test() ->
  T1 = {abs_nat, #{ "x" => tbool }, {var, "y"}},
  T2 = rename_term( "y", T1, "y$1" ),
  ?assertEqual( {abs_nat, #{ "x" => tbool }, {var, "y$1"}}, T2 ).

renaming_alters_name_in_signature_of_foreign_abstraction_test() ->
  T1 = {abs_for, #{ "x" => tbool }, tbool, bash, "blub"},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {abs_for, #{ "x$1" => tbool }, tbool, bash, "blub"}, T2 ).

renaming_leaves_unconcerned_untouched_in_foreign_abstraction_test() ->
  T1 = {abs_for, #{ "x" => tbool }, tbool, bash, "blub"},
  T2 = rename_term( "y", T1, "y$1" ),
  ?assertEqual( {abs_for, #{ "x" => tbool }, tbool, bash, "blub"}, T2 ).

renaming_is_delegated_to_left_in_app_test() ->
  T1 = {app, {var, "x"}, #{ "a" => {var, "y"} }},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {app, {var, "x$1"}, #{ "a" => {var, "y"} }}, T2 ).

renaming_is_delegated_to_value_in_right_of_app_test() ->
  T1 = {app, {var, "x"}, #{ "a" => {var, "y"} }},
  T2 = rename_term( "y", T1, "y$1" ),
  ?assertEqual( {app, {var, "x"}, #{ "a" => {var, "y$1"} }}, T2 ).

renaming_is_delegated_to_name_in_right_of_app_test() ->
  T1 = {app, {var, "x"}, #{ "a" => {var, "y"} }},
  T2 = rename_term( "a", T1, "a$1" ),
  ?assertEqual( {app, {var, "x"}, #{ "a$1" => {var, "y"} }}, T2 ).

fix_is_neutral_to_renaming_test() ->
  T1 = {fix, {var, "x"}},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {fix, {var, "x$1"}}, T2 ),
  ?assertEqual( T1, rename_term( "a", T1, "a$1" ) ).
  
renaming_alters_arg_names_in_zipwith_test() ->
  T1 = {zipwith, tbool, ["x"], {var, "y"}},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {zipwith, tbool, ["x$1"], {var, "y"}}, T2 ).

renaming_alters_term_in_zipwith_test() ->
  T1 = {zipwith, tbool, ["x"], {var, "y"}},
  T2 = rename_term( "y", T1, "y$1" ),
  ?assertEqual( {zipwith, tbool, ["x"], {var, "y$1"}}, T2 ).

renaming_alters_return_type_in_zipwith_test() ->
  T1 = {zipwith, {tabs, nat, #{ "a" => tstr }, tbool}, ["x"], {var, "y"}},
  T2 = rename_term( "a", T1, "a$1" ),
  Texp = {zipwith, {tabs, nat, #{ "a$1" => tstr }, tbool}, ["x"], {var, "y"}},
  ?assertEqual( Texp, T2 ).

renaming_leaves_unconcerned_untouched_in_zipwith_test() ->
  T1 = {zipwith, tbool, ["x"], {var, "y"}},
  T2 = rename_term( "a", T1, "a$1" ),
  ?assertEqual( T1, T2 ).

renaming_leaves_true_unaltered_test() ->
  ?assertEqual( true, rename_term( "x", true, "x$1" ) ).

renaming_leaves_false_unaltered_test() ->
  ?assertEqual( false, rename_term( "x", false, "x$1" ) ).

renaming_is_delegated_to_if_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {cnd, {var, "x$1"}, {var, "y"}, {var, "z"}}, T2 ).

renaming_is_delegated_to_then_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  T2 = rename_term( "y", T1, "y$1" ),
  ?assertEqual( {cnd, {var, "x"}, {var, "y$1"}, {var, "z"}}, T2 ).

renaming_is_delegated_to_else_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  T2 = rename_term( "z", T1, "z$1" ),
  ?assertEqual( {cnd, {var, "x"}, {var, "y"}, {var, "z$1"}}, T2 ).

renaming_leaves_unconcerned_untouched_in_cnd_test() ->
  T1 = {cnd, {var, "x"}, {var, "y"}, {var, "z"}},
  T2 = rename_term( "a", T1, "a$1" ),
  ?assertEqual( {cnd, {var, "x"}, {var, "y"}, {var, "z"}}, T2 ).

renaming_leaves_str_unaltered_test() ->
  ?assertEqual( {str, "blub"}, rename_term( "x", {str, "blub"}, "x$1" ) ).

renaming_leaves_file_unaltered_test() ->
  ?assertEqual( {file, "blub"}, rename_term( "x", {file, "blub"}, "x$1" ) ).

renaming_leaves_nil_unaltered_test() ->
  ?assertEqual( {nl, tbool}, rename_term( "x", {nl, tbool}, "x$1" ) ).

renaming_alters_type_in_nil_test() ->
  T1 = {nl, {tabs, nat, #{ "a" => tbool }, tstr}},
  Texp = {nl, {tabs, nat, #{ "a$1" => tbool }, tstr}},
  ?assertEqual( Texp, rename_term( "a", T1, "a$1" ) ).

renaming_is_delegated_to_head_in_cons_test() ->
  T1 = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  T2 = rename_term( "x", T1, "x$1" ),
  Texp = {cons, tbool, {var, "x$1"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  ?assertEqual( Texp, T2 ).

renaming_is_delegated_to_tail_in_cons_test() ->
  T1 = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  T2 = rename_term( "y", T1, "y$1" ),
  Texp = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y$1"}, {nl, tbool}}},
  ?assertEqual( Texp, T2 ).

renaming_alters_type_in_cons_test() ->
  Tp = {tabs, nat, #{ "a" => tbool }, tstr},
  Nil = {nl, Tp},
  Head = {abs_nat, #{ "a" => tbool }, {str, "blub"}},
  T1 = {cons, Tp, Head, Nil},
  TpExp = {tabs, nat, #{ "a$1" => tbool }, tstr},
  NilExp = {nl, TpExp},
  HeadExp = {abs_nat, #{ "a$1" => tbool }, {str, "blub"}},
  Texp = {cons, TpExp, HeadExp, NilExp},
  ?assertEqual( Texp, rename_term( "a", T1, "a$1" ) ).

renaming_leaves_unconcerned_untouched_in_cons_test() ->
  T1 = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  T2 = rename_term( "a", T1, "a$1" ),
  Texp = {cons, tbool, {var, "x"}, {cons, tbool, {var, "y"}, {nl, tbool}}},
  ?assertEqual( Texp, T2 ).

nenaming_alters_argument_in_isnil_test() ->
  T1 = {isnil, tbool, {var, "x"}},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {isnil, tbool, {var, "x$1"}}, T2 ),
  ?assertEqual( T1, rename_term( "a", T1, "a$1" ) ).

renaming_alters_type_in_isnil_test() ->
  T1 = {isnil, {tabs, nat, #{ "a" => tbool}, tstr}, {var, "x"}},
  T2 = rename_term( "a", T1, "a$1" ),
  Texp = {isnil, {tabs, nat, #{ "a$1" => tbool}, tstr}, {var, "x"}},
  ?assertEqual( Texp, T2 ).

renaming_is_delegated_to_elements_in_tuple_test() ->
  T1 = {tup, [{var, "x"}]},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {tup, [{var, "x$1"}]}, T2 ),
  ?assertEqual( T1, rename_term( "a", T1, "a$1" ) ).

proj_is_neutral_to_renaming_test() ->
  T1 = {proj, 1, {var, "x"}},
  T2 = rename_term( "x", T1, "x$1" ),
  ?assertEqual( {proj, 1, {var, "x$1"}}, T2 ),
  ?assertEqual( T1, rename_term( "a", T1, "a$1" ) ).

renaming_leaves_futures_untouched_test() ->
  T1 = {fut, tbool, 12},
  ?assertEqual( T1, rename_term( "x", T1, "x$1" ) ).

renaming_leaves_boolean_type_untouched_test() ->
  ?assertEqual( tbool, rename_type( "x", tbool, "x$1" ) ).

renaming_leaves_str_type_untouched_test() ->
  ?assertEqual( tstr, rename_type( "x", tstr, "x$1" ) ).

renaming_leaves_file_type_untouched_test() ->
  ?assertEqual( tfile, rename_type( "x", tfile, "x$1" ) ).

renaming_alters_name_in_signature_of_native_abstraction_type_test() ->
  Tp1 = {tabs, nat, #{ "a" => tbool }, tstr},
  Tp2 = rename_type( "a", Tp1, "a$1" ),
  Texp = {tabs, nat, #{ "a$1" => tbool }, tstr},
  ?assertEqual( Texp, Tp2 ).

renaming_alters_type_in_signature_of_native_abstraction_type_test() ->
  Tp1 = {tabs, nat, #{ "a" => {tabs, nat, #{ "b" => tbool }, tstr} }, tstr},
  Tp2 = rename_type( "b", Tp1, "b$1" ),
  Texp = {tabs, nat, #{ "a" => {tabs, nat, #{ "b$1" => tbool }, tstr} }, tstr},
  ?assertEqual( Texp, Tp2 ).

renaming_alters_return_type_of_native_abstraction_type_test() ->
  Tp1 = {tabs, nat, #{ "a" => tbool}, {tabs, nat, #{ "b" => tbool }, tstr}},
  Tp2 = rename_type( "b", Tp1, "b$1" ),
  Texp = {tabs, nat, #{ "a" => tbool }, {tabs, nat, #{ "b$1" => tbool }, tstr}},
  ?assertEqual( Texp, Tp2 ).

renaming_alters_argument_type_in_list_type_test() ->
  Tp1 = {tlst, {tabs, nat, #{ "a" => tbool }, tstr}},
  Tp2 = rename_type( "a", Tp1, "a$1" ),
  Texp = {tlst, {tabs, nat, #{ "a$1" => tbool }, tstr}},
  ?assertEqual( Texp, Tp2 ).

renaming_alters_argument_type_in_tuple_type_test() ->
  Tp1 = {ttup, [{tabs, nat, #{ "a" => tbool }, tstr}]},
  Tp2 = rename_type( "a", Tp1, "a$1" ),
  Texp = {ttup, [{tabs, nat, #{ "a$1" => tbool }, tstr}]},
  ?assertEqual( Texp, Tp2 ).

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
  T1 = {zipwith, tbool, ["a"], {var, "x"}},
  S = {var, "y"},
  T2 = subst( "x", S, T1 ),
  ?assertEqual( {zipwith, tbool, ["a"], S}, T2 ).

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

substitution_leaves_future_untouched_test() ->
  T1 = {fut, tbool, 12},
  ?assertEqual( T1, subst( "x", true, T1 ) ).


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

fix_with_nonnative_abstraction_is_untypable_test() ->
  T1 = {fix, {abs_for, #{ "f" => {tabs, nat, #{ "a" => tbool}, tstr} },
                       {tabs, nat, #{ "a" => tbool}, tstr},
                       bash,
                       "blub"}},
  Throw = {eforeign, fix, for},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

fix_with_multiple_bindings_is_untypable_test() ->
  T1 = {fix, {abs_nat, #{ "f" => {tabs, nat, #{ "a" => tbool}, tstr},
                          "g" => tbool },
                       {abs_for, #{ "a" => tbool }, tstr, bash, "blub"}}},
  Throw = {enonsingular, fix, ["f", "g"]},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

type_of_zipwith_is_derivable_test() ->
  T12 = {abs_nat, #{ "a" => tbool, "b" => tbool }, {str, "blub"}},
  T1 = {zipwith, tstr, ["a"], T12},
  T2 = {tabs, nat, #{ "a" => {tlst, tbool}, "b" => tbool }, {tlst, tstr}},
  ?assertEqual( T2, type_of( T1, #{} ) ).

unbound_arg_in_zipwith_is_untypable_test() ->
  T12 = {abs_nat, #{ "a" => tbool, "b" => tbool }, {str, "blub"}},
  T1 = {zipwith, tstr, ["c"], T12},
  Throw = {earg_undefined, zipwith, ["c"]},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

mismatching_types_in_zipwith_is_untypable_test() ->
  T12 = {abs_nat, #{ "a" => tbool, "b" => tbool }, {str, "blub"}},
  T1 = {zipwith, tbool, ["a"], T12},
  Throw = {ereturn_type, zipwith, {tbool, tstr}},
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
  Throw = {etail_type, cons, {{tlst, tstr}, {tlst, tbool}}},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

type_of_isnil_is_tbool_test() ->
  ?assertEqual( tbool, type_of( {isnil, tstr, {nl, tstr}}, #{} ) ).

isnil_type_mismatch_is_untypable_test() ->
  T1 = {isnil, tstr, {nl, tbool}},
  Throw = {elst_type, isnil, {{tlst, tstr}, {tlst, tbool}}},
  ?assertThrow( Throw, type_of( T1, #{} ) ).

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

type_of_fut_is_declared_type_test() ->
  T1 = {fut, tbool, 12},
  ?assertEqual( tbool, type_of( T1, #{} ) ).

foreign_call_with_arg_bound_to_abstraction_is_untypable_test() ->
  A1 = {abs_nat, #{}, {str, "bla"}},
  A2 = {abs_for, #{"x" => {tabs, nat, #{}, tstr}}, tbool, bash, "blub"},
  T = {app, A2, #{"x" => A1}},
  Throw = {earg_type, app, {"x", {tabs, nat, #{}, tstr}}},
  ?assertThrow( Throw, type_of( T, #{} ) ).

zipwith_with_empty_name_list_is_untypable_test() ->
  T = {zipwith, tbool, [], {abs_nat, #{ "x" => tbool }, {var, "x"}}},
  ?assertThrow( {ebad_namelst, zipwith, empty_namelst}, type_of( T, #{} ) ).


%% Step Relation

variable_is_no_redex_test() ->
  T = {var, "x"},
  ?assertThrow( {eundef, var, "x"}, type_of( T, #{} ) ),
  ?assertThrow( enorule, step( T, ?MU ) ).

native_abstraction_is_no_redex_test() ->
  T = {abs_nat, #{ "x" => tbool }, {str, "blub"}},
  ?assertEqual( {tabs, nat, #{ "x" => tbool }, tstr}, type_of( T, #{} ) ),
  ?assertThrow( enorule, step( T, ?MU ) ).

foreign_abstraction_is_no_redex_test() ->
  T = {abs_for, #{ "x" => tbool }, tstr, bash, "blub"},
  ?assertEqual( {tabs, for, #{ "x" => tbool }, tstr}, type_of( T, #{} ) ),
  ?assertThrow( enorule, step( T, ?MU ) ).

application_without_redexes_gets_stuck_test() ->
  A = {abs_for, #{ "x" => tbool}, tstr, bash, "bla"},
  X = {fut, tbool, 12},
  T = {app, A, #{ "x" => X }},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertThrow( enorule, step( T, ?MU ) ).

left_hand_side_of_application_is_evaluated_test() ->
  A1 = {abs_nat, #{ "x" => tbool}, {str, "bla"}},
  A2 = {abs_nat, #{ "x" => tbool}, {str, "blub"}},
  A = {cnd, true, A1, A2},
  T = {app, A, #{ "x" => true }},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( {app, A1, #{ "x" => true }}, step( T, ?MU ) ).

right_hand_side_of_application_with_native_abstraction_is_evaluated_test() ->
  A = {abs_nat, #{ "x" => tbool}, {str, "bla"}},
  X = {cnd, true, true, false},
  T = {app, A, #{ "x" => X }},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( {app, A, #{ "x" => true }}, step( T, ?MU ) ).

right_hand_side_of_application_with_foreign_abstraction_is_evaluated_test() ->
  A = {abs_for, #{ "x" => tbool}, tstr, bash, "bla"},
  X = {cnd, true, true, false},
  T = {app, A, #{ "x" => X }},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( {app, A, #{ "x" => true }}, step( T, ?MU ) ).

application_of_empty_native_abstraction_test() ->
  S = {str, "bla"},
  A = {abs_nat, #{}, S},
  T = {app, A, #{}},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( S, step( T, ?MU ) ).

application_leads_to_substitution_in_native_abstraction_body_test() ->
  S = {str, "bla"},
  A = {abs_nat, #{ "x" => tstr }, {var, "x"}},
  T = {app, A, #{ "x" => S }},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( {app, {abs_nat, #{}, S}, #{}}, step( T, ?MU ) ).

foreign_call_generates_future_test() ->
  A = {abs_for, #{ "x" => tstr }, tstr, bash, "blub"},
  X = {str, "bla"},
  T = {app, A, #{ "x" => X }},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertMatch( {fut, tstr, _}, step( T, ?MU ) ).

foreign_call_evaluates_right_hand_side_prior_to_generating_future_test() ->
  A = {abs_for, #{ "x" => tstr }, tstr, bash, "blub"},
  S = {str, "bla"},
  X = {cnd, true, S, {str, "lalala"}},
  T = {app, A, #{ "x" => X }},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( {app, A, #{ "x" => S }}, step( T, ?MU ) ).

fixpoint_is_substituted_into_body_test() ->
  T = {fix, {abs_nat, #{ "x" => tstr }, {str, "blub"}}},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( {str, "blub"}, step( T, ?MU ) ).

recursive_function_stays_constant_under_evaluation_test() ->
  T = {fix, {abs_nat, #{ "x" => tstr }, {var, "x"}}},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( T, step( T, ?MU ) ).

unevaluated_function_is_evaluated_in_fixpoint_test() ->
  T1 = {fix, {cnd, true, {abs_nat, #{ "x" => tstr }, {str, "bla"}},
                         {abs_nat, #{ "x" => tstr }, {str, "blub"}}}},
  T2 = {fix, {abs_nat, #{ "x" => tstr }, {str, "bla"}}},
  ?assertEqual( tstr, type_of( T1, #{} ) ),
  ?assertEqual( T2, step( T1, ?MU ) ).

zipwith_consumes_head_of_target_list_test() ->
  T12 = {abs_nat, #{ "x" => tbool }, {var, "x"}},
  Left = {zipwith, tbool, ["x"], T12},
  Right = #{ "x" => {cons, tbool, true, {cons, tbool, false, {nl, tbool}}} },
  T1 = {app, Left, Right},
  App = {app, T12, #{"x" => true}},
  Rest = {app, Left, #{ "x" => {cons, tbool, false, {nl, tbool}}}},
  T2 = {cons, tbool, App, Rest},
  ?assertEqual( {tlst, tbool}, type_of( T1, #{} ) ),
  ?assertEqual( T2, step( T1, ?MU ) ).

zipwith_stops_if_one_of_the_target_lists_is_nil_test() ->
  T12 = {abs_nat, #{ "x" => tbool, "y" => tbool }, {var, "x"}},
  Left = {zipwith, tbool, ["x", "y"], T12},
  Right = #{ "x" => {cons, tbool, true, {cons, tbool, false, {nl, tbool}}},
             "y" => {nl, tbool} },
  T1 = {app, Left, Right},
  T2 = {nl, tbool},
  ?assertEqual( {tlst, tbool}, type_of( T1, #{} ) ),
  ?assertEqual( T2, step( T1, ?MU ) ).

cnd_evaluates_if_term_test() ->
  T1 = {cnd, {cnd, true, true, false}, {str, "bla"}, {str, "blub"}},
  T2 = {cnd, true, {str, "bla"}, {str, "blub"}},
  ?assertEqual( tstr, type_of( T1, #{} ) ),
  ?assertEqual( T2, step( T1, ?MU ) ).

cnd_true_evaluates_then_term_test() ->
  T = {cnd, true, {str, "bla"}, {str, "blub"}},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( {str, "bla"}, step( T, ?MU ) ).

cnd_false_evaluates_else_term_test() ->
  T = {cnd, false, {str, "bla"}, {str, "blub"}},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( {str, "blub"}, step( T, ?MU ) ).

str_is_no_redex_test() ->
  ?assertThrow( enorule, step( {str, "bla"}, ?MU ) ).

file_is_no_redex_test() ->
  ?assertThrow( enorule, step( {file, "bla"}, ?MU ) ).

head_of_list_is_evaluated_test() ->
  T = {cons, tstr, {cnd, true, {str, "bla"}, {str, "blub"}}, {nl, tstr}},
  ?assertEqual( {tlst, tstr}, type_of( T, #{} ) ),
  ?assertEqual( {cons, tstr, {str, "bla"}, {nl, tstr}}, step( T, ?MU ) ).

tail_of_list_is_evaluated_test() ->
  T11 = {cons, tstr, {cnd, true, {str, "bla"}, {str, "blub"}}, {nl, tstr}},
  T1 = {cons, tstr, {str, "lala"}, T11},
  T2 = {cons, tstr, {str, "lala"}, {cons, tstr, {str, "bla"}, {nl, tstr}}},
  ?assertEqual( {tlst, tstr}, type_of( T1, #{} ) ),
  ?assertEqual( T2, step( T1, ?MU ) ).

nil_is_no_redex_test() ->
  ?assertThrow( enorule, step( nl( tstr() ), ?MU ) ).

isnil_of_nil_evaluates_to_true_test() ->
  T = {isnil, tstr, {nl, tstr}},
  ?assertEqual( tbool, type_of( T, #{} ) ),
  ?assertEqual( true, step( T, ?MU ) ).

isnil_of_cons_evaluates_to_false_test() ->
  T = {isnil, tstr, {cons, tstr, {str, "bla"}, {nl, tstr}}},
  ?assertEqual( tbool, type_of( T, #{} ) ),
  ?assertEqual( false, step( T, ?MU ) ).

isnil_of_redex_reduces_inner_term_test() ->
  T = {isnil, tstr, {cnd, true, {nl, tstr}, {nl, tstr}}},
  ?assertEqual( tbool, type_of( T, #{} ) ),
  ?assertEqual( {isnil, tstr, {nl, tstr}}, step( T, ?MU ) ).

projection_retrieves_corresponding_tuple_element_test() ->
  T = {proj, 2, {tup, [{str, "bla"}, {str, "blub"}]}},
  ?assertEqual( tstr, type_of( T, #{} ) ),
  ?assertEqual( {str, "blub"}, step( T, ?MU ) ).

tuple_evaluates_inner_terms_test() ->
  T = {tup, [{cnd, true, true, false}]},
  ?assertEqual( {ttup, [tbool]}, type_of( T, #{} ) ),
  ?assertEqual( {tup, [true]}, step( T, ?MU ) ).

fut_is_no_redex_test() ->
  ?assertThrow( enorule, step( {fut, tbool, 12}, ?MU ) ).


%% Values

native_abstraction_should_be_value_test() ->
  T = abs_nat( #{}, str( "blub" ) ),
  ?assertEqual( tabs_nat( #{}, tstr() ), type_of( T, #{} ) ),
  ?assert( is_value( T ) ).

foreign_abstraction_should_be_value_test() ->
  T = abs_for( #{}, tstr(), bash(), "blub" ),
  ?assertEqual( tabs_for( #{}, tstr() ), type_of( T, #{} ) ),
  ?assert( is_value( T ) ).

true_should_be_value_test() ->
  T = true(),
  ?assertEqual( tbool(), type_of( T, #{} ) ),
  ?assert( is_value( T ) ).

false_should_be_value_test() ->
  T = false(),
  ?assertEqual( tbool(), type_of( T, #{} ) ),
  ?assert( is_value( T ) ).

string_list_should_be_value_test() ->
  S = lst( tstr(), [str( "blub" )] ),
  ?assertEqual( tlst( tstr() ), type_of( S, #{} ) ),
  ?assert( is_value( S ) ).

nil_should_be_value_test() ->
  S = nl( tstr() ),
  ?assertEqual( tlst( tstr() ), type_of( S, #{} ) ),
  ?assert( is_value( S ) ).

string_tuple_should_be_value_test() ->
  T = tup( [str( "bla" ), file( "blub" ), true()] ),
  ?assertEqual( ttup( [tstr(), tfile(), tbool()] ), type_of( T, #{} ) ),
  ?assert( is_value( T ) ).

file_should_be_value_test() ->
  S = file( "blub" ),
  ?assertEqual( tfile(), type_of( S, #{} ) ),
  ?assert( is_value( S ) ).

string_should_be_value_test() ->
  S = str( "blub" ),
  ?assertEqual( tstr(), type_of( S, #{} ) ),
  ?assert( is_value( S ) ).

app_should_not_be_value_test() ->
  A = app( var( "f" ), #{} ),
  Ctx = #{ "f" => tabs_nat( #{}, tlst( tstr() ) ) },
  ?assertEqual( tlst( tstr() ), type_of( A, Ctx ) ),
  ?assertNot( is_value( A ) ).

cnd_should_not_be_value_test() ->
  NotIsNil = not_isnil( tstr(), lst( tstr(), [str( "a" )] ) ),
  C = cnd( NotIsNil, lst( tstr(), [str( "b" )] ), lst( tstr(), [str( "c" )] ) ),
  ?assertNot( is_value( C ) ).

isnil_should_not_be_value_test() ->
  T = isnil( tstr(), nl( tstr() ) ),
  ?assertEqual( tbool(), type_of( T, #{} ) ),
  ?assertNot( is_value( T ) ).

projection_should_not_be_value_test() ->
  T = proj( 1, tup( [str( "blub" )] ) ),
  ?assertEqual( tstr(), type_of( T, #{} ) ),
  ?assertNot( is_value( T ) ).

future_should_not_be_value_test() ->
  F = fut( tstr(), 12 ),
  ?assertEqual( tstr(), type_of( F, #{} ) ),
  ?assertNot( is_value( F ) ).

fixpoint_operator_should_not_be_value_test() ->
  T = fix( abs_nat( #{ "x" => tstr() }, str( "blub" ) ) ),
  ?assertEqual( tstr(), type_of( T, #{} ) ),
  ?assertNot( is_value( T ) ).

zipwith_operator_should_be_value_test() ->
  Abs = abs_nat( #{ "x" => tbool() }, str( "blub") ),
  T = zipwith( tstr(), ["x"], Abs ),
  ?assertEqual( tabs_nat( #{ "x" => tlst( tbool() ) }, tlst( tstr() ) ), type_of( T, #{} ) ),
  ?assert( is_value( T ) ).

variable_should_not_be_value_test() ->
  T = var( "x" ),
  ?assertEqual( tstr(), type_of( T, #{ "x" => tstr() } ) ),
  ?assertNot( is_value( T ) ).

-endif.


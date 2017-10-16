%%====================================================================
%% Static syntax
%%====================================================================

-type e() :: {str, string()}
           | {file, string()}

           | {lambda, ntv, [{atom(), string(), t()}], e()}
           | {e(), [{string(), e()}]}

           | {lambda, frn, string(), [{atom(), string(), u()}], u(), l(),
                      string()}
           | {fut, {{lambda, frn, string(), [{atom(), string(), u()}], u(),
                             l(), string()},
                    [{string(), e()}]}}

           | boolean()
           | {cnd, e(), e(), e()}.

-type v() :: {str, string()}
           | {file, string()}
           | {lambda, ntv, [{atom(), string(), t()}], e()}
           | {lambda, frn, string(), [{atom(), string(), u()}], u(), l(),
                      string()}
           | boolean().

-type t() :: 'Str'
           | 'File'
           | 'Bool'
           | {'Fn', ntv, [{string(), t()}], t()}
           | {'Fn', frn, [{string(), u()}], u()}.

-type u() :: 'Str'
           | 'File'
           | 'Bool'.

-type l() :: 'Bash'
           | 'Octave'
           | 'Perl'
           | 'Python'
           | 'R'.


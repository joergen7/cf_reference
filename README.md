# cf_reference
###### A reference implementation of the Cuneiform semantics.
[![Build Status](https://travis-ci.org/joergen7/cf_reference.svg?branch=master)](https://travis-ci.org/joergen7/cf_reference)

## Running All Diagnostics

The following diagnostics can be applied to this code base: The dialyzer applies a discrepancy analysis to the code base. Hereby, the function specifications are checked for consistency with the function implementations using success typing. The unit test suite that comes with this code base reflects the plausibility of typing, evaluation, substitution, and renaming. Finally, the Erlang Quick Check test generators and properties allow the assurance of Cuneiform's type safety using random testing.

    rebar3 do dialyzer, eunit, eqc

## System Requirements

- [Erlang](http://www.erlang.org) OTP 18.0 or higher
- [Rebar3](https://www.rebar3.org) 3.0.0 or higher
- [Erlang Quick Check (Mini)](http://www.quviq.com/index.html) 2.01.0 or higher
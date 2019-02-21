# Semantic Reference of the Cuneiform Distributed Programming Language

This is a specification of the Cuneiform distributed programming language created in [Redex](https://redex.racket-lang.org/).

This semantic reference defines an abstract syntax as a Redex language, a type system as judgment forms, a reduction relation as a notion of reduction and an evaluation context, and several examples for which we plot evaluation traces. The semantic reference comes with a unit test suite suitable to test new Cuneiform implementations.

Note that this reference defines only the semantics of the interpreter up to the interpreter's side of a communication protocol with a distributed execution environment.

## Rendering Reduction Traces

In DrRacket open the file `main.rkt` and run it by pressing `F5`. Several popups appear illustrating the reduction traces of selected Cuneiform expressions.

## Running the Test Suite

On the command line enter the following command while in the `cf_reference` directory:

    raco test -j 8 *.rkt

## Change Notes

The previous [0.1.0 release](https://github.com/joergen7/cf_reference/releases/tag/0.1.0) of this semantic reference includes property-based random tests based on [Erlang QuickCheck](http://www.quviq.com/products/erlang-quickcheck/). The current branch of the semantic reference provides only a unit test suite. We might add a property-based test scheme again later.

## System Requirements

- [Racket](http://www.racket-lang.org)

## Resources

- [joergen7/cuneiform](https://github.com/joergen7/cuneiform) Erlang-based Cuneiform implementation
- [Cuneiform semantics paper](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/computation-semantics-of-the-functional-scientific-workflow-language-cuneiform/1A3B8AB825939117C5BD9F850F63ADCC) published in the Journal of Functional Programming
- [Concrete syntax reference](https://www.cuneiform-lang.org/doc/syntax.html) in extended Backus-Naur form with railroad diagrams
- [Cuneiform website](https://cuneiform-lang.org)


## Authors

- Jörgen Brandt ([@joergen7](https://github.com/joergen7/)) [joergen.brandt@onlinehome.de](mailto:joergen.brandt@onlinehome.de)

## License

[Apache 2.0](https://www.apache.org/licenses/LICENSE-2.0.html)
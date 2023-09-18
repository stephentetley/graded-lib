# graded-lib

Experimental Flix library for graded functors, applicatives and monads.

Monads are indexed / graded by effects which are encapsulated by constructors. This contrasts
with Flix's stdlib Monad classes where effects always float "ambiently" to the righthand 
side of the type signatures.

`graded-lib` provides a set of classes defining the graded versions of the 
Functor-Applicative-Monad hierarchy and a provisional set of "amalgamated monads" in the 
`Graded` folder. These amalgamated monads are an alternative to monad transformers - 
Flix will provide user define effects at some point, defining a library of monad transformers
would not be a long term prospect. Instead `graded-lib` provides "ready rolled" monad-stacks
that can be used directly or wrapped with an `enum` newtype.

Monads are written in CPS to be stack safe.

Note - 18 September 2023. All the monads have been rewritten to minimize casting (casting had 
been causing a runtime crash). Version 0.8.0 has not been widely tested.

License: Apache 2.0

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

Note - 7 August 2023 - `graded-lib` is currently broken for Flix version 0.38.0 and higher. 
This is due to the use of unchecked casts and causes runtime not compile time failures. 

License: Apache 2.0

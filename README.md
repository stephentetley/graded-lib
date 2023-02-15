# graded-lib

Experimental Flix library for graded functors, applicatives and monads.

Monads are indexed / graded by effects which are encapsulated by constructors. This contrasts
with Flix's stdlib Monad classes where effects always float "ambiently" to the righthand 
side of the type signatures.

Monads are written in CPS to be stack safe.

License: Apache 2.0

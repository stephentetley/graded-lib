/*
 * Copyright 2023 Stephen Tetley
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


mod Graded {

    ///
    /// Codensity (CPS) / Error monad.
    /// 
    /// `ka` is the continuation answer type
    ///
    pub enum CodensityError[ka: Type, ef: Eff, a: Type](
        (a -> Result[String, ka] \ ef) -> Result[String, ka] \ ef)

    instance GradedFunctor[CodensityError[ka]] { 
        pub def map(f: a -> b \ ef1, m: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1, b] = 
            Graded.CodensityError.map(f, m)
    }

    instance GradedApplicative[CodensityError[ka]] { 
        pub def point(x: a): CodensityError[ka, ef, a] = 
            Graded.CodensityError.point(x)

        pub def ap(f: CodensityError[ka, ef1, a -> b \ ef2], m: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1 + ef2, b] = 
            Graded.CodensityError.ap(f, m)
    }

    instance GradedMonad[CodensityError[ka]] { 
        pub def flatMap(k: a -> CodensityError[ka, ef1, b] \ ef2, m: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1 + ef2, b] = 
            Graded.CodensityError.flatMap(k, m)
    }

    instance GradedZero[CodensityError[ka]] { 
        pub def empty(): CodensityError[ka, ef, a] = 
            Graded.CodensityError.empty()
    }

    // Orelse available for Evaluator because it is expected to only be reading the state

    instance GradedOr[CodensityError[ka]] { 
        pub def orelse(ma: CodensityError[ka, ef1, a], mb: CodensityError[ka, ef2, a]): CodensityError[ka, ef1 + ef2, a] =
            Graded.CodensityError.orelse(ma, mb)
    }
    
    instance GradedError[CodensityError[ka]] { 
        pub def throwError(msg: String): CodensityError[ka, ef, a] =
            Graded.CodensityError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1, a] = 
            Graded.CodensityError.mapError(f, ma)

        pub def catchError(ma: CodensityError[ka, ef, a], hdlr: String -> CodensityError[ka, ef1, a] \ ef2): CodensityError[ka, ef + ef1 + ef2, a] = 
            Graded.CodensityError.catchError(ma, hdlr)

        pub def reifyError(ma: CodensityError[ka, ef, a]): CodensityError[ka, ef, Result[String, a]] = 
            Graded.CodensityError.reifyError(ma)            
    }  


}

mod Graded.CodensityError {

    use Graded.CodensityError
    use Graded.CodensityError.{CodensityError}


    ///
    /// Helper function for the implementation of `map` and `ap` etc.
    ///
    def apply1(ma: CodensityError[ka, ef, a], k: a -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let CodensityError(ma1) = ma;
        ma1(k)


    def apply1WithHandler(ma: CodensityError[ka, ef, a], 
                            k: a -> Result[String, ka] \ ef, 
                            handleK: String -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let CodensityError(ma1) = ma;
        match ma1(k) {
            case Err(msg) => handleK(msg)
            case Ok(a)    => Ok(a)
        }

    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runCodensityError(ma: CodensityError[a, ef, a]): Result[String, a] \ ef =
        let CodensityError(f) = ma;
        let cont = a -> checked_ecast(Ok(a));
        f(cont)


    pub def point(x: a): CodensityError[ka, ef, a] = 
        CodensityError(k -> k(x))

    pub def map(f: a -> b \ ef1, ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1, b] =
        CodensityError(k ->
            apply1(unchecked_cast(ma as CodensityError[ka, ef + ef1, a]), a -> k(f(a)))
        )

    pub def ap(mf: CodensityError[ka, ef1, a -> b \ ef2], ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1 + ef2, b] =
        CodensityError(k ->
            apply1(unchecked_cast(mf as CodensityError[ka, ef + ef1 + ef2, a -> b \ ef2]), f ->
                apply1(unchecked_cast(ma as CodensityError[ka, ef + ef1 + ef2, a]), a ->
                    k(f(a))))
        )


    pub def flatMap(f: a -> CodensityError[ka, ef1, b] \ ef2, ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1 + ef2, b] =
        CodensityError(k ->
            apply1(unchecked_cast(ma as CodensityError[ka, ef + ef1 + ef2, a]), a ->
                apply1(unchecked_cast(f(a) as CodensityError[ka, ef + ef1 + ef2, b]), b ->
                    k(b)))
        )

    pub def throwError(msg: String): CodensityError[ka, ef, a] = 
        CodensityError(_ -> checked_ecast(Err(msg)))

    pub def catchError(ma: CodensityError[ka, ef, a], 
                        hdlr: String -> CodensityError[ka, ef1, a] \ ef2): CodensityError[ka, ef + ef1 + ef2, a] = 
        CodensityError(k -> 
            let CodensityError(ma1) = unchecked_cast(ma as CodensityError[ka, ef + ef1 + ef2, a]);
            match ma1(k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => { 
                    let CodensityError(hdlr1) = unchecked_cast(hdlr(msg) as CodensityError[ka, ef + ef1 + ef2, a]); 
                    hdlr1(k)
                }
            }
        )

    pub def mapError(f: String -> String \ ef1, ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1, a] = 
        CodensityError(k -> 
            apply1WithHandler(unchecked_cast(ma as CodensityError[ka, ef + ef1, a]), a -> k(a), msg -> checked_ecast(Err(f(msg))))
        )

    pub def reifyError(ma: CodensityError[ka, ef, a]): CodensityError[ka, ef, Result[String, a]] = 
        CodensityError(k -> 
            apply1WithHandler(ma, a -> k(Ok(a)), msg -> k(Err(msg)))
        )

    pub def empty(): CodensityError[ka, ef, a] = throwError("empty")

    pub def orelse(ma: CodensityError[ka, ef1, a], mb: CodensityError[ka, ef2, a]): CodensityError[ka, ef1 + ef2, a] =
        CodensityError(k ->
            apply1WithHandler(unchecked_cast(ma as CodensityError[ka, ef1 + ef2, a]), a -> k(a), _ -> 
                apply1(unchecked_cast(mb as CodensityError[ka, ef1 + ef2, a]), b -> k(b)))
        )

    pub def liftEffect(f: Unit -> a \ ef): CodensityError[ka, ef, a] = 
        CodensityError(k -> k(f()))

    pub def liftEffectResult(f: Unit -> Result[String, a] \ ef): CodensityError[ka, ef, a] = 
        CodensityError(k -> match f() { 
            case Ok(a)    => k(a)
            case Err(msg) => Err(msg)
        })

}

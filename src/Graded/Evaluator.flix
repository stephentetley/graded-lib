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
    /// Reader-Error like monad where the environment is "read-only mutable state" 
    /// (i.e mutation is expected but only before or after the Evaluator has run).
    ///
    /// `local` is not supported.
    /// 
    /// `ka` is the continuation answer type
    ///
    /// Ideally `vs` would be vs: Region -> Type with r: Region but this currently causes 
    /// a compiler crash (Flix issue #2113)
    ///    
    pub enum Evaluator[ka: Type, vs: Type, ef: Bool, a: Type](
        vs -> (a -> Result[String, ka] \ ef) -> Result[String, ka] \ ef
    )


    instance GradedFunctor[Evaluator[ka, vs]] { 
        pub def map(f: a -> b \ ef1, m: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef and ef1, b] = 
            Graded.Evaluator.map(f, m)
    }

    instance GradedApplicative[Evaluator[ka, vs]] { 
        pub def point(x: a): Evaluator[ka, vs, ef, a] = 
            Graded.Evaluator.point(x)

        pub def ap(f: Evaluator[ka, vs, ef1, a -> b \ ef2], m: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef and ef1 and ef2, b] = 
            Graded.Evaluator.ap(f, m)
    }

    instance GradedMonad[Evaluator[ka, vs]] { 
        pub def flatMap(k: a -> Evaluator[ka, vs, ef1, b] \ ef2, m: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef and ef1 and ef2, b] = 
            Graded.Evaluator.flatMap(k, m)
    }

    instance GradedZero[Evaluator[ka, vs]] { 
        pub def empty(): Evaluator[ka, vs, ef, a] = 
            Graded.Evaluator.empty()
    }

    // Orelse available for Evaluator because it is expected to only be reading the state

    instance GradedOr[Evaluator[ka, vs]] { 
        pub def orelse(ma: Evaluator[ka, vs, ef1, a], mb: Evaluator[ka, vs, ef2, a]): Evaluator[ka, vs, ef1 and ef2, a] =
            Graded.Evaluator.orelse(ma, mb)
    }
    
    instance GradedError[Evaluator[ka, vs]] { 
        pub def throwError(msg: String): Evaluator[ka, vs, ef, a] =
            Graded.Evaluator.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef and ef1, a] = 
            Graded.Evaluator.mapError(f, ma)

        pub def catchError(ma: Evaluator[ka, vs, ef, a], hdlr: String -> Evaluator[ka, vs, ef1, a] \ ef2): Evaluator[ka, vs, ef and ef1 and ef2, a] = 
            Graded.Evaluator.catchError(ma, hdlr)
        
        pub def reifyError(ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef, Result[String, a]] = 
            Graded.Evaluator.reifyError(ma)
    }  


}

mod Graded.Evaluator {

    use Graded.Evaluator
    use Graded.Evaluator.{Evaluator}


    ///
    /// Helper function for the implementation of `map` and `ap` etc.
    ///
    def apply1(ma: Evaluator[ka, vs, ef, a], 
                s: vs, 
                k: a -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let Evaluator(ma1) = ma;
        ma1(s, k)


    def apply1WithHandler(ma: Evaluator[ka, vs, ef, a], 
                            s: vs,
                            k: a -> Result[String, ka] \ ef, 
                            handleK: String -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let Evaluator(ma1) = ma;
        match ma1(s, k) {
            case Err(msg) => handleK(msg)
            case Ok(a)    => Ok(a)
        }



    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEvaluator(ma: Evaluator[a, vs, ef, a], s: vs): Result[String, a] \ ef =
        let Evaluator(f) = ma;
        let cont = a -> checked_ecast(Ok(a));
        f(s, cont)


    pub def point(x: a): Evaluator[ka, vs, ef, a] = 
        Evaluator((_, k) -> k(x))


    pub def map(f: a -> b \ ef1, ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef and ef1, b] =
        Evaluator((s, k) ->
            apply1(unchecked_cast(ma as Evaluator[ka, vs, ef and ef1, a]), s, a -> k(f(a)))
        )

    pub def ap(mf: Evaluator[ka, vs, ef1, a -> b \ ef2], 
                ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef and ef1 and ef2, b] =
        Evaluator((s, k) ->
            apply1(unchecked_cast(mf as Evaluator[ka, vs, ef and ef1 and ef2, a -> b \ ef2]), s, f ->
                apply1(unchecked_cast(ma as Evaluator[ka, vs, ef and ef1 and ef2, a]), s, a ->
                    k(f(a))))
        )


    pub def flatMap(f: a -> Evaluator[ka, vs, ef1, b] \ ef2, 
                    ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef and ef1 and ef2, b] =
        Evaluator((s, k) ->
            apply1(unchecked_cast(ma as Evaluator[ka, vs, ef and ef1 and ef2, a]), s, a ->
                apply1(unchecked_cast(f(a) as Evaluator[ka, vs, ef and ef1 and ef2, b]), s, b ->
                    k(b)))
        )

    pub def throwError(msg: String): Evaluator[ka, vs, ef, a] = 
        Evaluator((_, _) -> checked_ecast(Err(msg)))

    pub def catchError(ma: Evaluator[ka, vs, ef, a], 
                        hdlr: String -> Evaluator[ka, vs, ef1, a] \ ef2): Evaluator[ka, vs, ef and ef1 and ef2, a] = 
        Evaluator((s, k) -> 
            let Evaluator(ma1) = unchecked_cast(ma as Evaluator[ka, vs, ef and ef1 and ef2, a]);
            match ma1(s, k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => { 
                    let Evaluator(hdlr1) = unchecked_cast(hdlr(msg) as Evaluator[ka, vs, ef and ef1 and ef2, a]); 
                    hdlr1(s, k)
                }
            }
        )

    pub def mapError(f: String -> String \ ef1, ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef and ef1, a] = 
        Evaluator((s, k) -> 
            apply1WithHandler(unchecked_cast(ma as Evaluator[ka, vs, ef and ef1, a]), s, a -> k(a), msg -> checked_ecast(Err(f(msg))))
        )

    pub def reifyError(ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef, Result[String, a]] = 
        Evaluator((s, k) -> 
            apply1WithHandler(ma, s, a -> k(Ok(a)), msg -> k(Err(msg)))
        )

    pub def empty(): Evaluator[ka, vs, ef, a] = throwError("empty")

    pub def orelse(ma: Evaluator[ka, vs, ef1, a], mb: Evaluator[ka, vs, ef2, a]): Evaluator[ka, vs, ef1 and ef2, a] =
        Evaluator((s, k) ->
            apply1WithHandler(unchecked_cast(ma as Evaluator[ka, vs, ef1 and ef2, a]), s, a -> k(a), _ -> 
                apply1(unchecked_cast(mb as Evaluator[ka, vs, ef1 and ef2, a]), s, b -> k(b)))
        )


    pub def liftGetter(f: vs -> a \ ef): Evaluator[ka, vs, ef, a]= 
        Evaluator((s, k) ->
            try {
                let ans = f(s);
                k(ans)
            } catch {
                case ex: ##java.lang.Exception => 
                    import java.lang.Throwable.getMessage(): String \ {};
                    Err(getMessage(ex))
            }
        )


    // f should not throw an exception
    pub def liftGetterResult(f: vs -> Result[s, a] \ ef): Evaluator[ka, vs, ef, a] with ToString[s] = 
        Evaluator((s, k) ->
            match f(s) { 
                case Ok(a)    => k(a)
                case Err(err) => Err(ToString.toString(err))
            } 
        )


    pub def liftAction(f: Unit -> a \ ef): Evaluator[ka, vs, ef, a] = 
        Evaluator((_, k) ->
            let a = f(); 
            k(a)  
        )

    pub def liftActionResult(f: Unit -> Result[s, a] \ ef): Evaluator[ka, vs, ef, a] with ToString[s] = 
        Evaluator((_, k) ->
            match f() {
                case Ok(a)    => k(a)
                case Err(err) => Err(ToString.toString(err))
            } 
        )

}

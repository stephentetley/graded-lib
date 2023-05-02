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
    /// Reader and Error monad in codensity style to be stack safe.
    /// 
    /// `ka` is the continuation answer type
    ///
    pub enum EnvError[ka: Type, env: Type, ef: Bool, a: Type](
        env -> (a -> Result[String, ka] \ ef) -> Result[String, ka] \ ef)

    instance GradedFunctor[EnvError[ka, env]] { 
        pub def map(f: a -> b \ ef1, m: EnvError[ka, env, ef, a]): EnvError[ka, env, ef and ef1, b] = 
            Graded.EnvError.map(f, m)
    }

    instance GradedApplicative[EnvError[ka, env]] { 
        pub def point(x: a): EnvError[ka, env, ef, a] = 
            Graded.EnvError.point(x)

        pub def ap(f: EnvError[ka, env, ef1, a -> b \ ef2], m: EnvError[ka, env, ef, a]): EnvError[ka, env, ef and ef1 and ef2, b] = 
            Graded.EnvError.ap(f, m)
    }

    instance GradedMonad[EnvError[ka, env]] { 
        pub def flatMap(k: a -> EnvError[ka, env, ef1, b] \ ef2, m: EnvError[ka, env, ef, a]): EnvError[ka, env, ef and ef1 and ef2, b] = 
            Graded.EnvError.flatMap(k, m)
    }

    instance GradedZero[EnvError[ka, env]] { 
        pub def empty(): EnvError[ka, env, ef, a] = 
            Graded.EnvError.empty()
    }

    // Orelse available for Evaluator because it is expected to only be reading the state

    instance GradedOr[EnvError[ka, env]] { 
        pub def orelse(ma: EnvError[ka, env, ef1, a], mb: EnvError[ka, env, ef2, a]): EnvError[ka, env, ef1 and ef2, a] =
            Graded.EnvError.orelse(ma, mb)
    }
    
    instance GradedError[EnvError[ka, env]] { 
        pub def throwError(msg: String): EnvError[ka, env, ef, a] =
            Graded.EnvError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef and ef1, a] = 
            Graded.EnvError.mapError(f, ma)

        pub def catchError(ma: EnvError[ka, env, ef, a], hdlr: String -> EnvError[ka, env, ef1, a] \ ef2): EnvError[ka, env, ef and ef1 and ef2, a] = 
            Graded.EnvError.catchError(ma, hdlr)

        pub def reifyError(ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef, Result[String, a]] = 
            Graded.EnvError.reifyError(ma)
    }  


}

mod Graded.EnvError {

    use Graded.EnvError
    use Graded.EnvError.{EnvError}


    ///
    /// Helper function for the implementation of `map` and `ap` etc.
    ///
    def apply1(ma: EnvError[ka, env, ef, a], 
                e: env, 
                k: a -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let EnvError(ma1) = ma;
        ma1(e, k)


    def apply1WithHandler(ma: EnvError[ka, env, ef, a], 
                            e: env,
                            k: a -> Result[String, ka] \ ef, 
                            handleK: String -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let EnvError(ma1) = ma;
        match ma1(e, k) {
            case Err(msg) => handleK(msg)
            case Ok(a)    => Ok(a)
        }

    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEnvError(ma: EnvError[a, env, ef, a], e: env): Result[String, a] \ ef =
        let EnvError(f) = ma;
        let cont = a -> checked_ecast(Ok(a));
        f(e, cont)


    pub def point(x: a): EnvError[ka, env, ef, a] = 
        EnvError((_, k) -> k(x))

    pub def map(f: a -> b \ ef1, ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef and ef1, b] =
        EnvError((e, k) ->
            apply1(unchecked_cast(ma as EnvError[ka, env, ef and ef1, a]), e, a -> k(f(a)))
        )

    pub def ap(mf: EnvError[ka, env, ef1, a -> b \ ef2], ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef and ef1 and ef2, b] =
        EnvError((e, k) ->
            apply1(unchecked_cast(mf as EnvError[ka, env, ef and ef1 and ef2, a -> b \ ef2]), e, f ->
                apply1(unchecked_cast(ma as EnvError[ka, env, ef and ef1 and ef2, a]), e, a ->
                    k(f(a))))
        )


    pub def flatMap(f: a -> EnvError[ka, env, ef1, b] \ ef2, ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef and ef1 and ef2, b] =
        EnvError((e, k) ->
            apply1(unchecked_cast(ma as EnvError[ka, env, ef and ef1 and ef2, a]), e, a ->
                apply1(unchecked_cast(f(a) as EnvError[ka, env, ef and ef1 and ef2, b]), e, b ->
                    k(b)))
        )

    pub def throwError(msg: String): EnvError[ka, env, ef, a] = 
        EnvError((_, _) -> checked_ecast(Err(msg)))

    pub def catchError(ma: EnvError[ka, env, ef, a], 
                        hdlr: String -> EnvError[ka, env, ef1, a] \ ef2): EnvError[ka, env, ef and ef1 and ef2, a] = 
        EnvError((e, k) -> 
            let EnvError(ma1) = unchecked_cast(ma as EnvError[ka, env, ef and ef1 and ef2, a]);
            match ma1(e, k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => { 
                    let EnvError(hdlr1) = unchecked_cast(hdlr(msg) as EnvError[ka, env, ef and ef1 and ef2, a]); 
                    hdlr1(e, k)
                }
            }
        )

    pub def mapError(f: String -> String \ ef1, ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef and ef1, a] = 
        EnvError((e, k) -> 
            apply1WithHandler(unchecked_cast(ma as EnvError[ka, env, ef and ef1, a]), e, a -> k(a), msg -> checked_ecast(Err(f(msg))))
        )

    pub def reifyError(ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef, Result[String, a]] = 
        EnvError((e, k) -> 
            apply1WithHandler(ma, e, a -> k(Ok(a)), msg -> k(Err(msg)))
        )

    pub def empty(): EnvError[ka, env, ef, a] = throwError("empty")

    pub def orelse(ma: EnvError[ka, env, ef1, a], mb: EnvError[ka, env, ef2, a]): EnvError[ka, env, ef1 and ef2, a] =
        EnvError((e, k) ->
            apply1WithHandler(unchecked_cast(ma as EnvError[ka, env, ef1 and ef2, a]), e, a -> k(a), _ -> 
                apply1(unchecked_cast(mb as EnvError[ka, env, ef1 and ef2, a]), e, b -> k(b)))
        )


    pub def liftGetter(f: env -> a \ ef): EnvError[ka, env, ef, a]= 
        EnvError((e, k) ->
            try {
                let ans = f(e);
                k(ans)
            } catch {
                case ex: ##java.lang.Exception => 
                    import java.lang.Throwable.getMessage(): String \ {};
                    Err(getMessage(ex))
            }
        )

    // f should not throw an exception
    pub def liftGetterResult(f: env -> Result[e, a] \ ef): EnvError[ka, env, ef, a] with ToString[e] = 
        EnvError((e, k) ->
            match f(e) { 
                case Ok(a)    => k(a)
                case Err(err) => Err(ToString.toString(err))
            } 
        )

    pub def liftAction(f: Unit -> a \ ef): EnvError[ka, env, ef, a] = 
        EnvError((_, k) ->
            let a = f(); 
            k(a)  
        )

    pub def liftActionResult(f: Unit -> Result[e, a] \ ef): EnvError[ka, env, ef, a] with ToString[e] = 
        EnvError((_, k) ->
            match f() {
                case Ok(a)    => k(a)
                case Err(err) => Err(ToString.toString(err))
            } 
        )

    pub def ask(): EnvError[ka, env, ef, env] = 
        EnvError((e, k) -> k(e))

    pub def asks(f: env -> a \ ef): EnvError[ka, env, ef, a] = 
        EnvError((e, k) -> k(f(e)))

    pub def local(f: env -> env1 \ ef1, ma: EnvError[ka, env1, ef, a]): EnvError[ka, env, ef and ef1, a] = 
        EnvError((e, k) -> 
            apply1(unchecked_cast(ma as EnvError[ka, env1, ef and ef1, a]), f(e), a1 -> 
                k(a1))
        )


}

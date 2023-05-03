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
    /// The EnvStateError monad is in the codensity style to be stack safe.
    /// 
    /// `ka` is the continuation answer type
    ///
    pub enum EnvStateError[ka: Type, env: Type, st: Type, ef: Bool, a: Type](
        env -> st -> (a -> st -> Result[String, ka] \ ef) -> Result[String, ka] \ ef)

    instance GradedFunctor[EnvStateError[ka, env, st]] { 
        pub def map(f: a -> b \ ef1, m: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef and ef1, b] = 
            Graded.EnvStateError.map(f, m)
    }

    instance GradedApplicative[EnvStateError[ka, env, st]] { 
        pub def point(x: a): EnvStateError[ka, env, st, ef, a] = 
            Graded.EnvStateError.point(x)

        pub def ap(f: EnvStateError[ka, env, st, ef1, a -> b \ ef2], m: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef and ef1 and ef2, b] = 
            Graded.EnvStateError.ap(f, m)
    }

    instance GradedMonad[EnvStateError[ka, env, st]] { 
        pub def flatMap(k: a -> EnvStateError[ka, env, st, ef1, b] \ ef2, m: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef and ef1 and ef2, b] = 
            Graded.EnvStateError.flatMap(k, m)
    }

    // Orelse available for EnvStateError because state is pure (so resetable).

    instance GradedOr[EnvStateError[ka, env, st]] { 
        pub def orelse(ma: EnvStateError[ka, env, st, ef1, a], mb: EnvStateError[ka, env, st, ef2, a]): EnvStateError[ka, env, st, ef1 and ef2, a] =
            Graded.EnvStateError.orelse(ma, mb)
    }


    instance GradedError[EnvStateError[ka, env, st]] { 
        pub def throwError(msg: String): EnvStateError[ka, env, st, ef, a] =
            Graded.EnvStateError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef and ef1, a] = 
            Graded.EnvStateError.mapError(f, ma)

        pub def catchError(ma: EnvStateError[ka, env, st, ef, a], hdlr: String -> EnvStateError[ka, env, st, ef1, a] \ ef2): EnvStateError[ka, env, st, ef and ef1 and ef2, a] = 
            Graded.EnvStateError.catchError(ma, hdlr)
        
        pub def reifyError(ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef, Result[String, a]] = 
            Graded.EnvStateError.reifyError(ma)
    }  


}

mod Graded.EnvStateError {


    use Graded.EnvStateError
    use Graded.EnvStateError.{EnvStateError}


    ///
    /// Helper function for the implementation of `map` and `ap` etc.
    ///
    def apply1(ma: EnvStateError[ka, env, st, ef, a], 
                e: env,
                s: st, 
                k: a -> st -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let EnvStateError(ma1) = ma;
        ma1(e, s, k)

    def apply1WithHandler(ma: EnvStateError[ka, env, st, ef, a], 
                            e: env,
                            s: st, 
                            k: a -> st -> Result[String, ka] \ ef, 
                            handleK: String -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let EnvStateError(ma1) = ma;
        match ma1(e, s, k) {
            case Err(msg) => handleK(msg)
            case Ok(a)    => Ok(a)
        }



    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEnvStateError(ma: EnvStateError[(s, a), env, s, ef, a], e: env, st: s): Result[String, (s, a)] \ ef =
        let EnvStateError(f) = ma;
        let cont = (a, s1) -> checked_ecast (Ok(s1, a));
        f(e, st, cont)

    pub def point(x: a): EnvStateError[ka, env, st, ef, a] = 
        EnvStateError((_, s, k) -> k(x, s))

    pub def map(f: a -> b \ ef1, ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef and ef1, b] =
        EnvStateError((e, s, k) ->
            apply1(unchecked_cast(ma as EnvStateError[ka, env, st, ef and ef1, a]), e, s, (a, s1) -> {let b = f(a); k(b, s1)})
        )

    pub def ap(mf: EnvStateError[ka, env, st, ef1, a -> b \ ef2], ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef and ef1 and ef2, b] =
        EnvStateError((e, s, k) ->
            apply1(unchecked_cast(mf as EnvStateError[ka, env, st, ef and ef1 and ef2, a -> b \ ef2]), e, s, (f, s1) ->
                apply1(unchecked_cast(ma as EnvStateError[ka, env, st, ef and ef1 and ef2, a]), e, s1, (a, s2) ->
                    k(f(a), s2)))
        )

    pub def flatMap(f: a -> EnvStateError[ka, env, st, ef1, b] \ ef2, ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef and ef1 and ef2, b] =
        EnvStateError((e, s, k) ->
            apply1(unchecked_cast(ma as EnvStateError[ka, env, st, ef and ef1 and ef2, a]), e, s, (a, s1) ->
                apply1(unchecked_cast(f(a) as EnvStateError[ka, env, st, ef and ef1 and ef2, b]), e, s1, (b, s2) ->
                    k(b, s2)))
        )

    pub def orelse(ma: EnvStateError[ka, env, st, ef1, a], mb: EnvStateError[ka, env, st, ef2, a]): EnvStateError[ka, env, st, ef1 and ef2, a] =
        EnvStateError((e, s, k) ->
            apply1WithHandler(unchecked_cast(ma as EnvStateError[ka, env, st, ef1 and ef2, a]), e, s, a ->  k(a), _ -> 
                apply1(unchecked_cast(mb as EnvStateError[ka, env, st, ef1 and ef2, a]), e, s, b -> k(b)))
        )

    pub def throwError(msg: String): EnvStateError[ka, env, s, ef, a] = 
        EnvStateError((_, _, _) -> checked_ecast(Err(msg)))

    pub def catchError(ma: EnvStateError[ka, env, st, ef, a], 
                        hdlr: String -> EnvStateError[ka, env, st, ef1, a] \ ef2): EnvStateError[ka, env, st, ef and ef1 and ef2, a] = 
        EnvStateError((e, s, k) -> 
            let EnvStateError(ma1) = unchecked_cast(ma as EnvStateError[ka, env, st, ef and ef1 and ef2, a]);
            match ma1(e, s, k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => { 
                    let EnvStateError(hdlr1) = unchecked_cast(hdlr(msg) as EnvStateError[ka, env, st, ef and ef1 and ef2, a]); 
                    hdlr1(e, s, k)
                }
            }
        )

    pub def mapError(f: String -> String \ ef1, ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef and ef1, a] = 
        EnvStateError((e, s, k) -> 
            apply1WithHandler(unchecked_cast(ma as EnvStateError[ka, env, st, ef and ef1, a]), e, s, k, msg -> checked_ecast(Err(f(msg))))
        )
   
    pub def reifyError(ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef, Result[String, a]] = 
        EnvStateError((e, s, k) -> 
            apply1WithHandler(ma, e, s, a -> k(Ok(a)), msg -> k(Err(msg), s))
        )


    pub def update(f: st -> st \ ef): EnvStateError[ka, env, st, ef, Unit] = 
        EnvStateError((_, s, k) -> 
            k((), f(s))
        )


    pub def put(s: st): EnvStateError[ka, env, st, ef, Unit] = 
        EnvStateError((_, _, k) -> 
            k((), s)
        )

    // polymorphic `ef`...
    pub def get(): EnvStateError[ka, env, st, ef, st] = 
        EnvStateError((_, s, k) -> 
            k(s, s)
        )


    pub def gets(proj: st -> a \ ef): EnvStateError[ka, env, st, ef, a] = 
        EnvStateError((_, s, k) -> 
            k(proj(s), s)
        )

    pub def ask(): EnvStateError[ka, env, st, ef, env] = 
        EnvStateError((e, s, k) -> 
            k(e, s)
        )

    pub def asks(proj: env -> a \ ef): EnvStateError[ka, env, st, ef, a] = 
        EnvStateError((e, s, k) -> 
            k(proj(e), s)
        )

    pub def local(f: env -> env1 \ ef1, ma: EnvStateError[ka, env1, st, ef, a]): EnvStateError[ka, env, st, ef and ef1, a] = 
        EnvStateError((e, s, k) -> 
            apply1(unchecked_cast(ma as EnvStateError[ka, env1, st, ef and ef1, a]), f(e), s, (a1, s1) -> 
                k(a1, s1)
            )
        )
}
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
    pub enum EnvStateError[ka: Type, env: Type, st: Type, _ef: Eff, a: Type](
        env -> st -> (a -> st -> Result[String, ka] \ IO) -> Result[String, ka] \ IO)

    instance GradedFunctor[EnvStateError[ka, env, st]] { 
        pub def map(f: a -> b \ ef1, m: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef + ef1, b] = 
            Graded.EnvStateError.map(f, m)
    }

    instance GradedApplicative[EnvStateError[ka, env, st]] { 
        pub def point(x: a): EnvStateError[ka, env, st, ef, a] = 
            Graded.EnvStateError.point(x)

        pub def ap(f: EnvStateError[ka, env, st, ef1, a -> b \ ef2], m: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef + ef1 + ef2, b] = 
            Graded.EnvStateError.ap(f, m)
    }

    instance GradedMonad[EnvStateError[ka, env, st]] { 
        pub def flatMap(k: a -> EnvStateError[ka, env, st, ef1, b] \ ef2, m: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef + ef1 + ef2, b] = 
            Graded.EnvStateError.flatMap(k, m)
    }

    // Orelse available for EnvStateError because state is pure (so resetable).

    instance GradedOr[EnvStateError[ka, env, st]] { 
        pub def orelse(ma: EnvStateError[ka, env, st, ef1, a], mb: EnvStateError[ka, env, st, ef2, a]): EnvStateError[ka, env, st, ef1 + ef2, a] =
            Graded.EnvStateError.orelse(ma, mb)
    }


    instance GradedError[EnvStateError[ka, env, st]] { 
        pub def throwError(msg: String): EnvStateError[ka, env, st, ef, a] =
            Graded.EnvStateError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef + ef1, a] = 
            Graded.EnvStateError.mapError(f, ma)

        pub def catchError(ma: EnvStateError[ka, env, st, ef, a], hdlr: String -> EnvStateError[ka, env, st, ef1, a] \ ef2): EnvStateError[ka, env, st, ef + ef1 + ef2, a] = 
            Graded.EnvStateError.catchError(ma, hdlr)
        
        pub def reifyError(ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef, Result[String, a]] = 
            Graded.EnvStateError.reifyError(ma)
    }  


}

mod Graded.EnvStateError {


    use Graded.EnvStateError
    use Graded.EnvStateError.{EnvStateError}


    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEnvStateError(ma: EnvStateError[(s, a), env, s, ef, a], e: env, st: s): Result[String, (s, a)] \ ef =
        let EnvStateError(f) = ma;
        let cont = (a, s1) -> checked_ecast (Ok(s1, a));
        unchecked_cast(f(e, st, cont) as _ \ ef)

    pub def point(x: a): EnvStateError[ka, env, st, ef, a] = 
        def run(_, s, k) = k(x, s);
        EnvStateError(run)

    pub def map(f: a -> b \ ef1, ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef + ef1, b] =
        let EnvStateError(g) = ma;
        def run(e, s, k) = g(e, s, (a, s1) -> k(f(a), s1));
        EnvStateError(run)

    pub def ap(mf: EnvStateError[ka, env, st, ef1, a -> b \ ef2], ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef + ef1 + ef2, b] =
        let EnvStateError(g) = mf;
        let EnvStateError(h) = ma;
        def run(e, s, k) = g(e, s, (f1, s1) -> h(e, s1, (a, s2) -> k(f1(a), s2)));
        EnvStateError(run)

    pub def flatMap(f: a -> EnvStateError[ka, env, st, ef1, b] \ ef2, ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef + ef1 + ef2, b] =
        let EnvStateError(g) = ma;
        def run(e, s, k) = g(e, s, (a, s1) -> {let EnvStateError(h) = f(a); h(e, s1, k)});
        EnvStateError(run)

    pub def throwError(msg: String): EnvStateError[ka, env, s, ef, a] = 
        def run(_, _, _) = checked_ecast(Err(msg));
        EnvStateError(run)

    pub def catchError(ma: EnvStateError[ka, env, st, ef, a], 
                        hdlr: String -> EnvStateError[ka, env, st, ef1, a] \ ef2): EnvStateError[ka, env, st, ef + ef1 + ef2, a] = 
        let EnvStateError(g) = ma;
        def run(e, s, k) = match g(e, s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let EnvStateError(h) = hdlr(msg); h(e, s, k)}
        };
        EnvStateError(run)

    pub def mapError(f: String -> String \ ef1, ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef + ef1, a] = 
        let EnvStateError(g) = ma;
        def run(e, s, k) = match g(e, s, k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        EnvStateError(run)

    pub def reifyError(ma: EnvStateError[ka, env, st, ef, a]): EnvStateError[ka, env, st, ef, Result[String, a]] = 
        let EnvStateError(g) = ma;
        def run(e, s, k) = match g(e, s, (a, s1) -> k(Ok(a), s1)) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg), s)
        };
        EnvStateError(run)

    pub def orelse(ma: EnvStateError[ka, env, st, ef1, a], mb: EnvStateError[ka, env, st, ef2, a]): EnvStateError[ka, env, st, ef1 + ef2, a] =
        let EnvStateError(g) = ma;
        let EnvStateError(h) = mb;
        def run(e, s, k) = match g(e, s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(_)   => h(e, s, k)
        };
        EnvStateError(run)


    pub def update(f: st -> st \ ef1): EnvStateError[ka, env, st, ef + ef1, Unit] = 
        def run(_, s, k) = k((), f(s));
        EnvStateError(run)


    pub def put(s: st): EnvStateError[ka, env, st, ef, Unit] = 
        def run(_, _, k) = k((), s);
        EnvStateError(run)

    // polymorphic `ef`...
    pub def get(): EnvStateError[ka, env, st, ef, st] = 
        def run(_, s, k) = k(s, s);
        EnvStateError(run)

    
    pub def gets(proj: st -> a \ ef1): EnvStateError[ka, env, st, ef + ef1, a] = 
        def run(_, s, k) = k(proj(s), s);
        EnvStateError(run)

    pub def ask(): EnvStateError[ka, env, st, ef, env] = 
        def run(e, s, k) = k(e, s);
        EnvStateError(run)

    pub def asks(proj: env -> a \ ef1): EnvStateError[ka, env, st, ef + ef1, a] = 
        def run(e, s, k) = k(proj(e), s);
        EnvStateError(run)

    pub def local(f: env -> env1 \ ef1, ma: EnvStateError[ka, env1, st, ef, a]): EnvStateError[ka, env, st, ef + ef1, a] = 
        let EnvStateError(g) = ma;
        def run(e, s, k) = g(f(e), s, k);
        EnvStateError(run)

}

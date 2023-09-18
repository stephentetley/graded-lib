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
    /// Reader-Reader-Error like monad where the second environment is "read-only mutable state" 
    /// / "volatile state" (i.e mutation is expected but only before or after the EnvEvaluator has run).
    ///
    /// `local` is not supported for the second environment.
    /// 
    /// `ka` is the continuation answer type
    ///
    /// Ideally `vs` would be vs: Region -> Type with r: Region but this currently causes 
    /// a compiler crash (Flix issue #2113)
    ///    
    pub enum EnvEvaluator[ka: Type, env: Type, vs: Type, _ef: Eff, a: Type](
        env -> vs -> (a -> Result[String, ka] \ IO) -> Result[String, ka] \ IO
    )


    instance GradedFunctor[EnvEvaluator[ka, env, vs]] { 
        pub def map(f: a -> b \ ef1, m: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef + ef1, b] = 
            Graded.EnvEvaluator.map(f, m)
    }

    instance GradedApplicative[EnvEvaluator[ka, env, vs]] { 
        pub def point(x: a): EnvEvaluator[ka, env, vs, ef, a] = 
            Graded.EnvEvaluator.point(x)

        pub def ap(f: EnvEvaluator[ka, env, vs, ef1, a -> b \ ef2], m: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef + ef1 + ef2, b] = 
            Graded.EnvEvaluator.ap(f, m)
    }

    instance GradedMonad[EnvEvaluator[ka, env, vs]] { 
        pub def flatMap(k: a -> EnvEvaluator[ka, env, vs, ef1, b] \ ef2, m: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef + ef1 + ef2, b] = 
            Graded.EnvEvaluator.flatMap(k, m)
    }

    instance GradedZero[EnvEvaluator[ka, env, vs]] { 
        pub def empty(): EnvEvaluator[ka, env, vs, ef, a] = 
            Graded.EnvEvaluator.empty()
    }

    // Orelse available for EnvEvaluator because it is expected to only be reading the state

    instance GradedOr[EnvEvaluator[ka, env, vs]] { 
        pub def orelse(ma: EnvEvaluator[ka, env, vs, ef1, a], mb: EnvEvaluator[ka, env, vs, ef2, a]): EnvEvaluator[ka, env, vs, ef1 + ef2, a] =
            Graded.EnvEvaluator.orelse(ma, mb)
    }
    
    instance GradedError[EnvEvaluator[ka, env, vs]] { 
        pub def throwError(msg: String): EnvEvaluator[ka, env, vs, ef, a] =
            Graded.EnvEvaluator.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef + ef1, a] = 
            Graded.EnvEvaluator.mapError(f, ma)

        pub def catchError(ma: EnvEvaluator[ka, env, vs, ef, a], hdlr: String -> EnvEvaluator[ka, env, vs, ef1, a] \ ef2): EnvEvaluator[ka, env, vs, ef + ef1 + ef2, a] = 
            Graded.EnvEvaluator.catchError(ma, hdlr)
        
        pub def reifyError(ma: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef, Result[String, a]] = 
            Graded.EnvEvaluator.reifyError(ma)
    }  


}

mod Graded.EnvEvaluator {

    use Graded.EnvEvaluator
    use Graded.EnvEvaluator.{EnvEvaluator}


    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEnvEvaluator(ma: EnvEvaluator[a, env, vs, ef, a], e: env, s: vs): Result[String, a] \ ef =
        let EnvEvaluator(f) = ma;
        let cont = a -> checked_ecast(Ok(a));
        unchecked_cast(f(e, s, cont) as _ \ ef)


    pub def point(x: a): EnvEvaluator[ka, env, vs, ef, a] = 
        def run(_, _, k) = k(x);
        EnvEvaluator(run)


    pub def map(f: a -> b \ ef1, ma: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef + ef1, b] =
        let EnvEvaluator(g) = ma;
        def run(e, s, k) = g(e, s, a -> k(f(a)));
        EnvEvaluator(run)

    pub def ap(mf: EnvEvaluator[ka, env, vs, ef1, a -> b \ ef2], 
                ma: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef + ef1 + ef2, b] =
        let EnvEvaluator(g) = mf;
        let EnvEvaluator(h) = ma;
        def run(e, s, k) = g(e, s, f -> h(e, s, a -> k(f(a))));
        EnvEvaluator(run)

    pub def flatMap(f: a -> EnvEvaluator[ka, env, vs, ef1, b] \ ef2, 
                    ma: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef + ef1 + ef2, b] =
        let EnvEvaluator(g) = ma;
        def run(e, s, k) = g(e, s, a -> {let EnvEvaluator(h) = f(a); h(e, s, k)});
        EnvEvaluator(run)

    pub def throwError(msg: String): EnvEvaluator[ka, env, vs, ef, a] = 
        def run(_, _, _) = checked_ecast(Err(msg));
        EnvEvaluator(run)

    pub def catchError(ma: EnvEvaluator[ka, env, vs, ef, a], 
                        hdlr: String -> EnvEvaluator[ka, env, vs, ef1, a] \ ef2): EnvEvaluator[ka, env, vs, ef + ef1 + ef2, a] = 
        let EnvEvaluator(g) = ma;
        def run(e, s, k) = match g(e, s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let EnvEvaluator(h) = hdlr(msg); h(e, s, k)}
        };
        EnvEvaluator(run)

    pub def mapError(f: String -> String \ ef1, ma: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef + ef1, a] = 
        let EnvEvaluator(g) = ma;
        def run(e, s, k) = match g(e, s, k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        EnvEvaluator(run)

    pub def reifyError(ma: EnvEvaluator[ka, env, vs, ef, a]): EnvEvaluator[ka, env, vs, ef, Result[String, a]] = 
        let EnvEvaluator(g) = ma;
        def run(e, s, k) = match g(e, s, a -> k(Ok(a))) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg))
        };
        EnvEvaluator(run)

    pub def empty(): EnvEvaluator[ka, env, vs, ef, a] = throwError("empty")

    pub def orelse(ma: EnvEvaluator[ka, env, vs, ef1, a], mb: EnvEvaluator[ka, env, vs, ef2, a]): EnvEvaluator[ka, env, vs, ef1 + ef2, a] =
        let EnvEvaluator(g) = ma;
        let EnvEvaluator(h) = mb;
        def run(e, s, k) = match g(e, s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(_)   => h(e, s, k)
        };
        EnvEvaluator(run)


    pub def liftGetter(f: vs -> a \ ef): EnvEvaluator[ka, env, vs, ef, a]= 
        def run(_, s, k) = try {
            let ans = f(s);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        EnvEvaluator(run)

    pub def liftGetterWithEnv(f: env -> vs -> a \ ef): EnvEvaluator[ka, env, vs, ef, a]= 
        def run(e, s, k) = try {
            let ans = f(e, s);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        EnvEvaluator(run)

    // f should not throw an exception
    pub def liftGetterResult(f: vs -> Result[s, a] \ ef): EnvEvaluator[ka, env, vs, ef, a] with ToString[s] = 
        def run(_, s, k) =  match f(s) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        EnvEvaluator(run)

    // f should not throw an exception
    pub def liftGetterResultWithEnv(f: env -> vs -> Result[s, a] \ ef): EnvEvaluator[ka, env, vs, ef, a] with ToString[s] = 
        def run(e, s, k) =  match f(e, s) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        EnvEvaluator(run)

    pub def liftAction(f: Unit -> a \ ef): EnvEvaluator[ka, env, vs, ef, a] = 
        def run(_, _, k) = {
            let a = f(); 
            k(a)  
        };
        EnvEvaluator(run)

    pub def liftActionResult(f: Unit -> Result[s, a] \ ef): EnvEvaluator[ka, env, vs, ef, a] with ToString[s] = 
        def run(_, _, k) = match f() {
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        EnvEvaluator(run)


    pub def ask(): EnvEvaluator[ka, env, vs, ef, env]  = 
        def run(e, _, k) = k(e);
        EnvEvaluator(run)

    pub def asks(f: env -> a \ ef1): EnvEvaluator[ka, env, vs, ef + ef1, a]  = 
        def run(e, _, k) = k(f(e));
        EnvEvaluator(run)

    pub def local(f: env -> env1 \ ef1, ma: EnvEvaluator[ka, env1, vs, ef, a]): EnvEvaluator[ka, env, vs, ef + ef1, a] = 
        let EnvEvaluator(g) = ma;
        def run(e, s, k) = g(f(e), s, k);
        EnvEvaluator(run)

}

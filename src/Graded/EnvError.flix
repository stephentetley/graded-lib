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
    pub enum EnvError[ka: Type, env: Type, _ef: Eff, a: Type](
        env -> (a -> Result[String, ka] \ IO) -> Result[String, ka] \ IO)

    instance GradedFunctor[EnvError[ka, env]] { 
        pub def map(f: a -> b \ ef1, m: EnvError[ka, env, ef, a]): EnvError[ka, env, ef + ef1, b] = 
            Graded.EnvError.map(f, m)
    }

    instance GradedApplicative[EnvError[ka, env]] { 
        pub def point(x: a): EnvError[ka, env, ef, a] = 
            Graded.EnvError.point(x)

        pub def ap(f: EnvError[ka, env, ef1, a -> b \ ef2], m: EnvError[ka, env, ef, a]): EnvError[ka, env, ef + ef1 + ef2, b] = 
            Graded.EnvError.ap(f, m)
    }

    instance GradedMonad[EnvError[ka, env]] { 
        pub def flatMap(k: a -> EnvError[ka, env, ef1, b] \ ef2, m: EnvError[ka, env, ef, a]): EnvError[ka, env, ef + ef1 + ef2, b] = 
            Graded.EnvError.flatMap(k, m)
    }

    instance GradedZero[EnvError[ka, env]] { 
        pub def empty(): EnvError[ka, env, ef, a] = 
            Graded.EnvError.empty()
    }

    // Orelse available for Evaluator because it is expected to only be reading the state

    instance GradedOr[EnvError[ka, env]] { 
        pub def orelse(ma: EnvError[ka, env, ef1, a], mb: EnvError[ka, env, ef2, a]): EnvError[ka, env, ef1 + ef2, a] =
            Graded.EnvError.orelse(ma, mb)
    }
    
    instance GradedError[EnvError[ka, env]] { 
        pub def throwError(msg: String): EnvError[ka, env, ef, a] =
            Graded.EnvError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef + ef1, a] = 
            Graded.EnvError.mapError(f, ma)

        pub def catchError(ma: EnvError[ka, env, ef, a], hdlr: String -> EnvError[ka, env, ef1, a] \ ef2): EnvError[ka, env, ef + ef1 + ef2, a] = 
            Graded.EnvError.catchError(ma, hdlr)

        pub def reifyError(ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef, Result[String, a]] = 
            Graded.EnvError.reifyError(ma)
    }  


}

mod Graded.EnvError {

    use Graded.EnvError
    use Graded.EnvError.{EnvError}



    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEnvError(ma: EnvError[a, env, ef, a], e: env): Result[String, a] \ ef =
        let EnvError(f) = ma;
        let cont = a -> checked_ecast(Ok(a));
        unchecked_cast(f(e, cont) as _ \ ef)


    pub def point(x: a): EnvError[ka, env, ef, a] = 
        EnvError((_, k) -> k(x))

    pub def map(f: a -> b \ ef1, ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef + ef1, b] =
        let EnvError(g) = ma;
        def run(e, k) = g(e, a -> k(f(a)));
        EnvError(run)

    pub def ap(mf: EnvError[ka, env, ef1, a -> b \ ef2], ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef + ef1 + ef2, b] =
        let EnvError(g) = mf;
        let EnvError(h) = ma;
        def run(e, k) = g(e, f1 -> h(e, a -> k(f1(a))));
        EnvError(run)

    pub def flatMap(f: a -> EnvError[ka, env, ef1, b] \ ef2, ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef + ef1 + ef2, b] =
        let EnvError(g) = ma;
        def run(e, k) = g(e, a -> {let EnvError(h) = f(a); h(e, k)});
        EnvError(run)

    pub def throwError(msg: String): EnvError[ka, env, ef, a] = 
        EnvError((_, _) -> checked_ecast(Err(msg)))

    pub def catchError(ma: EnvError[ka, env, ef, a], 
                        hdlr: String -> EnvError[ka, env, ef1, a] \ ef2): EnvError[ka, env, ef + ef1 + ef2, a] = 
        let EnvError(g) = ma;
        def run(e, k) = match g(e, k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let EnvError(h) = hdlr(msg); h(e, k)}
        };
        EnvError(run)


    pub def mapError(f: String -> String \ ef1, ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef + ef1, a] = 
        let EnvError(g) = ma;
        def run(e, k) = match g(e, k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        EnvError(run)

    pub def reifyError(ma: EnvError[ka, env, ef, a]): EnvError[ka, env, ef, Result[String, a]] = 
       let EnvError(g) = ma;
        def run(e, k) = match g(e, a -> k(Ok(a))) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg))
        };
        EnvError(run)

    pub def empty(): EnvError[ka, env, ef, a] = throwError("empty")

    pub def orelse(ma: EnvError[ka, env, ef1, a], mb: EnvError[ka, env, ef2, a]): EnvError[ka, env, ef1 + ef2, a] =
        let EnvError(g) = ma;
        let EnvError(h) = mb;
        def run(e, k) = match g(e, k) {
            case Ok(ans)  => Ok(ans)
            case Err(_)   => h(e, k)
        };
        EnvError(run)

    pub def liftGetter(f: env -> a \ ef): EnvError[ka, env, ef, a]= 
        def run(e, k) = try {
            let ans = f(e);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        EnvError(run)
    

    // f should not throw an exception
    pub def liftGetterResult(f: env -> Result[e, a] \ ef): EnvError[ka, env, ef, a] with ToString[e] = 
        def run(e, k) =  match f(e) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        EnvError(run)

    pub def liftAction(f: Unit -> a \ ef): EnvError[ka, env, ef, a] = 
        def run(_, k) = {
            let a = f(); 
            k(a)  
        };
        EnvError(run)

    pub def liftActionResult(f: Unit -> Result[e, a] \ ef): EnvError[ka, env, ef, a] with ToString[e] = 
        def run(_, k) = match f() {
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        EnvError(run)

    pub def ask(): EnvError[ka, env, ef, env] = 
        def run(e, k) = k(e);
        EnvError(run)

    pub def asks(f: env -> a \ ef1): EnvError[ka, env, ef + ef1, a] = 
        def run(e, k) = k(f(e));
        EnvError(run)

    pub def local(f: env -> env1 \ ef1, ma: EnvError[ka, env1, ef, a]): EnvError[ka, env, ef + ef1, a] = 
        let EnvError(g) = ma;
        def run(e, k) = g(f(e), k);
        EnvError(run)


}

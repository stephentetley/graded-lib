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
    /// Mutable State (no local), Env/Reader (with local), and Error 
    /// monad in codensity style to be stack safe.
    /// 
    /// `ka` is the continuation answer type
    ///
    pub enum EnvMutStateError[ka: Type, env: Type, st: Type, _ef: Eff, a: Type](
        env -> st -> (a -> Result[String, ka] \ IO) -> Result[String, ka] \ IO)


    instance GradedFunctor[EnvMutStateError[ka, env, st]] { 
        pub def map(f: a -> b \ ef1, m: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef + ef1, b] = 
            Graded.EnvMutStateError.map(f, m)
    }

    instance GradedApplicative[EnvMutStateError[ka, env, st]] { 
        pub def point(x: a): EnvMutStateError[ka, env, st, ef, a] = 
            Graded.EnvMutStateError.point(x)

        pub def ap(f: EnvMutStateError[ka, env, st, ef1, a -> b \ ef2], 
                    m: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef + ef1 + ef2, b] = 
            Graded.EnvMutStateError.ap(f, m)
    }

    instance GradedMonad[EnvMutStateError[ka, env, st]] { 
        pub def flatMap(k: a -> EnvMutStateError[ka, env, st, ef1, b] \ ef2, 
                        m: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef + ef1 + ef2, b] = 
            Graded.EnvMutStateError.flatMap(k, m)
    }


    /// No `MonadOr` for EnvMutStateError because updated state cannot be unwound.
    
    instance GradedError[EnvMutStateError[ka, env, st]] { 
        pub def throwError(msg: String): EnvMutStateError[ka, env, st, ef, a] =
            Graded.EnvMutStateError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, 
                            ma: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef + ef1, a] = 
            Graded.EnvMutStateError.mapError(f, ma)

        pub def catchError(ma: EnvMutStateError[ka, env, st, ef, a], 
                            hdlr: String -> EnvMutStateError[ka, env, st, ef1, a] \ ef2): EnvMutStateError[ka, env, st, ef + ef1 + ef2, a] = 
            Graded.EnvMutStateError.catchError(ma, hdlr)

        pub def reifyError(ma: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef, Result[String, a]] = 
            Graded.EnvMutStateError.reifyError(ma)
    }  


}

mod Graded.EnvMutStateError {

    use Graded.EnvMutStateError
    use Graded.EnvMutStateError.{EnvMutStateError}



    ///
    /// Returns the result of applying `ma` to the state `vs` and env `e`.
    ///
    pub def runEnvMutStateError(ma: EnvMutStateError[a, env, st, ef, a],
                                e: env,
                                vs: st): Result[String, a] \ ef =
        let EnvMutStateError(f) = ma;
        let cont = a -> checked_ecast(Ok(a));
        unchecked_cast(f(e, vs, cont) as _ \ ef)


    pub def point(x: a): EnvMutStateError[ka, env, ef, st, a] = 
        def run(_, _, k) = k(x);
        EnvMutStateError(run)

    pub def map(f: a -> b \ ef1, ma: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef + ef1, b] =
        let EnvMutStateError(g) = ma;
        def run(e, s, k) = g(e, s, a -> k(f(a)));
        EnvMutStateError(run)

    pub def ap(mf: EnvMutStateError[ka, env, st, ef1, a -> b \ ef2], 
                ma: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef + ef1 + ef2, b] =
        let EnvMutStateError(g) = mf;
        let EnvMutStateError(h) = ma;
        def run(e, s, k) = g(e, s, f1 -> h(e, s, a -> k(f1(a))));
        EnvMutStateError(run)


    pub def flatMap(f: a -> EnvMutStateError[ka, env, st, ef1, b] \ ef2, 
                    ma: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef + ef1 + ef2, b] =
        let EnvMutStateError(g) = ma;
        def run(e, s, k) = g(e, s, a -> {let EnvMutStateError(h) = f(a); h(e, s, k)});
        EnvMutStateError(run)

    pub def throwError(msg: String): EnvMutStateError[ka, env, st, ef, a] = 
        def run(_, _, _) = checked_ecast(Err(msg));
        EnvMutStateError(run)


    pub def catchError(ma: EnvMutStateError[ka, env, st, ef, a], 
                        hdlr: String -> EnvMutStateError[ka, env, st, ef1, a] \ ef2): EnvMutStateError[ka, env, st, ef + ef1 + ef2, a] = 
        let EnvMutStateError(g) = ma;
        def run(e, s, k) = match g(e, s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let EnvMutStateError(h) = hdlr(msg); h(e, s, k)}
        };
        EnvMutStateError(run)


    pub def mapError(f: String -> String \ ef1, ma: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef + ef1, a] = 
        let EnvMutStateError(g) = ma;
        def run(e, s, k) = match g(e, s, k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        EnvMutStateError(run)
   

    pub def reifyError(ma: EnvMutStateError[ka, env, st, ef, a]): EnvMutStateError[ka, env, st, ef, Result[String, a]] = 
        let EnvMutStateError(g) = ma;
        def run(e, s, k) = match g(e, s, a -> k(Ok(a))) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg))
        };
        EnvMutStateError(run)

    pub def liftGetter(f: env -> st -> a \ ef): EnvMutStateError[ka, env, st, ef, a] = 
        def run(e, s, k) = try {
            let ans = f(e, s);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        EnvMutStateError(run)

    // f should not throw an exception
    pub def liftGetterResult(f: env -> st -> Result[e, a] \ ef): EnvMutStateError[ka, env, st, ef, a] with ToString[e] = 
        def run(e, s, k) =  match f(e, s) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        EnvMutStateError(run)

    pub def liftSetter!(f: env -> st -> a \ ef): EnvMutStateError[ka, env, st, ef, a] = 
        def run(e, s, k) = try {
            let a = f(e, s); 
            k(a)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        EnvMutStateError(run)


    // f should not throw an exception
    pub def liftSetterResult!(f: env -> st -> Result[e, a] \ ef): EnvMutStateError[ka, env, st, ef, a] with ToString[e] = 
        def run(e, s, k) = match f(e, s) {
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        EnvMutStateError(run)

    pub def liftAction(f: Unit -> a \ ef): EnvMutStateError[ka, env, st, ef, a] = 
        def run(_, _, k) = {
            let a = f();
            k(a)
        };
        EnvMutStateError(run)

    pub def liftActionResult(f: Unit -> Result[e, a] \ ef): EnvMutStateError[ka, env, st, ef, a] with ToString[e] = 
        def run(_, _, k) = match f() {
            case Ok(a)  => k(a)
            case Err(e) => Err(ToString.toString(e))
        };
        EnvMutStateError(run)

    pub def ask(): EnvMutStateError[ka, env, st, ef, env]  = 
        def run(e, _, k) = k(e);
        EnvMutStateError(run)

    pub def asks(f: env -> a \ ef1): EnvMutStateError[ka, env, st, ef + ef1, a]  = 
        def run(e, _, k) = k(f(e));
        EnvMutStateError(run)

    pub def local(f: env -> env1 \ ef1, ma: EnvMutStateError[ka, env1, st, ef, a]): EnvMutStateError[ka, env, st, ef + ef1, a] = 
        let EnvMutStateError(g) = ma;
        def run (e, vs, k) = g(f(e), vs, k);
        EnvMutStateError(run)

}

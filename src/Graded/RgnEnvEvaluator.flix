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
    /// Version of `EnvEvaluator` with region capabilities
    ///    
    pub enum RgnEnvEvaluator[ka: Type, r: Region, env: Type, vs: Type, _ef: Eff, a: Type](
        Region[r] -> env -> vs -> (a -> Result[String, ka] \ IO) -> Result[String, ka] \ IO
    )


    instance GradedFunctor[RgnEnvEvaluator[ka, r, env, vs]] { 
        pub def map(f: a -> b \ ef1, m: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef + ef1, b] = 
            Graded.RgnEnvEvaluator.map(f, m)
    }

    instance GradedApplicative[RgnEnvEvaluator[ka, r, env, vs]] { 
        pub def point(x: a): RgnEnvEvaluator[ka, r, env, vs, ef, a] = 
            Graded.RgnEnvEvaluator.point(x)

        pub def ap(f: RgnEnvEvaluator[ka, r, env, vs, ef1, a -> b \ ef2], m: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef + ef1 + ef2, b] = 
            Graded.RgnEnvEvaluator.ap(f, m)
    }

    instance GradedMonad[RgnEnvEvaluator[ka, r, env, vs]] { 
        pub def flatMap(k: a -> RgnEnvEvaluator[ka, r, env, vs, ef1, b] \ ef2, m: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef + ef1 + ef2, b] = 
            Graded.RgnEnvEvaluator.flatMap(k, m)
    }

    instance GradedZero[RgnEnvEvaluator[ka, r, env, vs]] { 
        pub def empty(): RgnEnvEvaluator[ka, r, env, vs, ef, a] = 
            Graded.RgnEnvEvaluator.empty()
    }

    // Orelse available for RgnEnvEvaluator because it is expected to only be reading the state

    instance GradedOr[RgnEnvEvaluator[ka, r, env, vs]] { 
        pub def orelse(ma: RgnEnvEvaluator[ka, r, env, vs, ef1, a], mb: RgnEnvEvaluator[ka, r, env, vs, ef2, a]): RgnEnvEvaluator[ka, r, env, vs, ef1 + ef2, a] =
            Graded.RgnEnvEvaluator.orelse(ma, mb)
    }
    
    instance GradedError[RgnEnvEvaluator[ka, r, env, vs]] { 
        pub def throwError(msg: String): RgnEnvEvaluator[ka, r, env, vs, ef, a] =
            Graded.RgnEnvEvaluator.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef + ef1, a] = 
            Graded.RgnEnvEvaluator.mapError(f, ma)

        pub def catchError(ma: RgnEnvEvaluator[ka, r, env, vs, ef, a], hdlr: String -> RgnEnvEvaluator[ka, r, env, vs, ef1, a] \ ef2): RgnEnvEvaluator[ka, r, env, vs, ef + ef1 + ef2, a] = 
            Graded.RgnEnvEvaluator.catchError(ma, hdlr)
        
        pub def reifyError(ma: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef, Result[String, a]] = 
            Graded.RgnEnvEvaluator.reifyError(ma)
    }  


}

mod Graded.RgnEnvEvaluator {

    use Graded.RgnEnvEvaluator
    use Graded.RgnEnvEvaluator.{RgnEnvEvaluator}

    use Graded.EnvEvaluator
    use Graded.EnvEvaluator.{EnvEvaluator}


    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def localRgn(rc: Region[r], ma: RgnEnvEvaluator[a, r, env, vs, ef, a]): EnvEvaluator[a, env, vs, ef, a] \ r =
        let RgnEnvEvaluator(g) = ma;
        def run(e, s, k) = g(rc, e, s, k);
        checked_ecast(EnvEvaluator(run))


    pub def liftEnvEvaluator(ma: EnvEvaluator[ka, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef, a] =
        let EnvEvaluator(g) = ma;
        def run(_, e, s, k) = g(e, s, k);
        RgnEnvEvaluator(run)

    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runRgnEnvEvaluator(ma: RgnEnvEvaluator[a, r, env, vs, ef, a], rc: Region[r], e: env, s: vs): Result[String, a] \ ef =
        let RgnEnvEvaluator(f) = ma;
        let cont = a -> checked_ecast(Ok(a));
        unchecked_cast(f(rc, e, s, cont) as _ \ ef)


    pub def point(x: a): RgnEnvEvaluator[ka, r, env, vs, ef, a] = 
        def run(_, _, _, k) = k(x);
        RgnEnvEvaluator(run)

    pub def map(f: a -> b \ ef1, ma: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef + ef1, b] =
        let RgnEnvEvaluator(g) = ma;
        def run(rc, e, s, k) = g(rc, e, s, a -> k(f(a)));
        RgnEnvEvaluator(run)

    pub def ap(mf: RgnEnvEvaluator[ka, r, env, vs, ef1, a -> b \ ef2], 
                ma: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef + ef1 + ef2, b] =
        let RgnEnvEvaluator(g) = mf;
        let RgnEnvEvaluator(h) = ma;
        def run(rc, e, s, k) = g(rc, e, s, f -> h(rc, e, s, a -> k(f(a))));
        RgnEnvEvaluator(run)


    pub def flatMap(f: a -> RgnEnvEvaluator[ka, r, env, vs, ef1, b] \ ef2, 
                    ma: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef + ef1 + ef2, b] =
        let RgnEnvEvaluator(g) = ma;
        def run(rc, e, s, k) = g(rc, e, s, a -> {let RgnEnvEvaluator(h) = f(a); h(rc, e, s, k)});
        RgnEnvEvaluator(run)

    pub def throwError(msg: String): RgnEnvEvaluator[ka, r, env, vs, ef, a] = 
        def run(_, _, _, _) = checked_ecast(Err(msg));
        RgnEnvEvaluator(run)

    pub def catchError(ma: RgnEnvEvaluator[ka, r, env, vs, ef, a], 
                        hdlr: String -> RgnEnvEvaluator[ka, r, env, vs, ef1, a] \ ef2): RgnEnvEvaluator[ka, r, env, vs, ef + ef1 + ef2, a] = 
        let RgnEnvEvaluator(g) = ma;
        def run(rc, e, s, k) = match g(rc, e, s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let RgnEnvEvaluator(h) = hdlr(msg); h(rc, e, s, k)}
        };
        RgnEnvEvaluator(run)

    pub def mapError(f: String -> String \ ef1, ma: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef + ef1, a] = 
        let RgnEnvEvaluator(g) = ma;
        def run(rc, e, s, k) = match g(rc, e, s, k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        RgnEnvEvaluator(run)

    pub def reifyError(ma: RgnEnvEvaluator[ka, r, env, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef, Result[String, a]] = 
        let RgnEnvEvaluator(g) = ma;
        def run(rc, e, s, k) = match g(rc, e, s, a -> k(Ok(a))) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg))
        };
        RgnEnvEvaluator(run)

    pub def empty(): RgnEnvEvaluator[ka, r, env, vs, ef, a] = throwError("empty")

    pub def orelse(ma: RgnEnvEvaluator[ka, r, env, vs, ef1, a], mb: RgnEnvEvaluator[ka, r, env, vs, ef2, a]): RgnEnvEvaluator[ka, r, env, vs, ef1 + ef2, a] =
        let RgnEnvEvaluator(g) = ma;
        let RgnEnvEvaluator(h) = mb;
        def run(rc, e, s, k) = match g(rc, e, s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(_)   => h(rc, e, s, k)
        };
        RgnEnvEvaluator(run)


    pub def liftGetter(f: vs -> a \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a]= 
        def run(_, _, s, k) = try {
            let ans = f(s);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        RgnEnvEvaluator(run)

    pub def liftGetterWithEnv(f: env -> vs -> a \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a]= 
        def run(_, e, s, k) = try {
            let ans = f(e, s);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        RgnEnvEvaluator(run)


    pub def liftGetterWithRgn(f: Region[r] -> vs -> a \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a]= 
        def run(rc, _, s, k) = try {
            let ans = f(rc, s);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        RgnEnvEvaluator(run)

    // f should not throw an exception
    pub def liftGetterResult(f: vs -> Result[s, a] \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a] with ToString[s] = 
        def run(_, _, s, k) =  match f(s) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        RgnEnvEvaluator(run)

    // f should not throw an exception
    pub def liftGetterResultWithEnv(f: env -> vs -> Result[s, a] \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a] with ToString[s] = 
        def run(_, e, s, k) =  match f(e, s) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        RgnEnvEvaluator(run)

    // f should not throw an exception
    pub def liftGetterResultWithRgn(f: Region[r] -> vs -> Result[err, a] \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a] with ToString[err] = 
        def run(rc, _, s, k) =  match f(rc, s) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        RgnEnvEvaluator(run)

    pub def liftAction(f: Unit -> a \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a] = 
        def run(_, _, _, k) = {
            let a = f(); 
            k(a)  
        };
        RgnEnvEvaluator(run)


    pub def liftActionWithRgn(f: Region[r] -> a \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a] = 
        def run(rc, _, _, k) = {
            let a = f(rc); 
            k(a)  
        };
        RgnEnvEvaluator(run)

    pub def liftActionResult(f: Unit -> Result[s, a] \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a] with ToString[s] = 
        def run(_, _, _, k) = match f() {
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        RgnEnvEvaluator(run)

    pub def liftActionResultWithRgn(f: Region[r] -> Result[s, a] \ ef): RgnEnvEvaluator[ka, r, env, vs, ef, a] with ToString[s] = 
        def run(rc, _, _, k) = match f(rc) {
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        RgnEnvEvaluator(run)

    pub def ask(): RgnEnvEvaluator[ka, r, env, vs, ef, env]  = 
        def run(_, e, _, k) = k(e);
        RgnEnvEvaluator(run)

    pub def asks(f: env -> a \ ef1): RgnEnvEvaluator[ka, r, env, vs, ef + ef1, a]  = 
        def run(_, e, _, k) = k(f(e));
        RgnEnvEvaluator(run)

    pub def local(f: env -> env1 \ ef1, ma: RgnEnvEvaluator[ka, r, env1, vs, ef, a]): RgnEnvEvaluator[ka, r, env, vs, ef + ef1, a] = 
        let RgnEnvEvaluator(g) = ma;
        def run(rc, e, s, k) = g(rc, f(e), s, k);
        RgnEnvEvaluator(run)


}

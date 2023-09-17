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
    pub enum Evaluator[ka: Type, vs: Type, _ef: Eff, a: Type](
        vs -> (a -> Result[String, ka] \ IO) -> Result[String, ka] \ IO
    )


    instance GradedFunctor[Evaluator[ka, vs]] { 
        pub def map(f: a -> b \ ef1, m: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef + ef1, b] = 
            Graded.Evaluator.map(f, m)
    }

    instance GradedApplicative[Evaluator[ka, vs]] { 
        pub def point(x: a): Evaluator[ka, vs, ef, a] = 
            Graded.Evaluator.point(x)

        pub def ap(f: Evaluator[ka, vs, ef1, a -> b \ ef2], m: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef + ef1 + ef2, b] = 
            Graded.Evaluator.ap(f, m)
    }

    instance GradedMonad[Evaluator[ka, vs]] { 
        pub def flatMap(k: a -> Evaluator[ka, vs, ef1, b] \ ef2, m: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef + ef1 + ef2, b] = 
            Graded.Evaluator.flatMap(k, m)
    }

    instance GradedZero[Evaluator[ka, vs]] { 
        pub def empty(): Evaluator[ka, vs, ef, a] = 
            Graded.Evaluator.empty()
    }

    // Orelse available for Evaluator because it is expected to only be reading the state

    instance GradedOr[Evaluator[ka, vs]] { 
        pub def orelse(ma: Evaluator[ka, vs, ef1, a], mb: Evaluator[ka, vs, ef2, a]): Evaluator[ka, vs, ef1 + ef2, a] =
            Graded.Evaluator.orelse(ma, mb)
    }
    
    instance GradedError[Evaluator[ka, vs]] { 
        pub def throwError(msg: String): Evaluator[ka, vs, ef, a] =
            Graded.Evaluator.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef + ef1, a] = 
            Graded.Evaluator.mapError(f, ma)

        pub def catchError(ma: Evaluator[ka, vs, ef, a], hdlr: String -> Evaluator[ka, vs, ef1, a] \ ef2): Evaluator[ka, vs, ef + ef1 + ef2, a] = 
            Graded.Evaluator.catchError(ma, hdlr)
        
        pub def reifyError(ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef, Result[String, a]] = 
            Graded.Evaluator.reifyError(ma)
    }  


}

mod Graded.Evaluator {

    use Graded.Evaluator
    use Graded.Evaluator.{Evaluator}



    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEvaluator(ma: Evaluator[a, vs, ef, a], s: vs): Result[String, a] \ ef =
        let Evaluator(f) = ma;
        let cont = a -> checked_ecast(Ok(a));
        unchecked_cast(f(s, cont) as _ \ ef)


    pub def point(x: a): Evaluator[ka, vs, ef, a] = 
        def run(_, k) = k(x);
        Evaluator(run)


    pub def map(f: a -> b \ ef1, ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef + ef1, b] =
        let Evaluator(g) = ma;
        def run(e, k) = g(e, a -> k(f(a)));
        Evaluator(run)

    pub def ap(mf: Evaluator[ka, vs, ef1, a -> b \ ef2], 
                ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef + ef1 + ef2, b] =
        let Evaluator(g) = mf;
        let Evaluator(h) = ma;
        def run(e, k) = g(e, f1 -> h(e, a -> k(f1(a))));
        Evaluator(run)


    pub def flatMap(f: a -> Evaluator[ka, vs, ef1, b] \ ef2, 
                    ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef + ef1 + ef2, b] =
        let Evaluator(g) = ma;
        def run(e, k) = g(e, a -> {let Evaluator(h) = f(a); h(e, k)});
        Evaluator(run)

    pub def throwError(msg: String): Evaluator[ka, vs, ef, a] = 
        def run(_, _) = checked_ecast(Err(msg));
        Evaluator(run)

    pub def catchError(ma: Evaluator[ka, vs, ef, a], 
                        hdlr: String -> Evaluator[ka, vs, ef1, a] \ ef2): Evaluator[ka, vs, ef + ef1 + ef2, a] = 
        let Evaluator(g) = ma;
        def run(e, k) = match g(e, k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let Evaluator(h) = hdlr(msg); h(e, k)}
        };
        Evaluator(run)

    pub def mapError(f: String -> String \ ef1, ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef + ef1, a] = 
        let Evaluator(g) = ma;
        def run(e, k) = match g(e, k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        Evaluator(run)

    pub def reifyError(ma: Evaluator[ka, vs, ef, a]): Evaluator[ka, vs, ef, Result[String, a]] = 
        let Evaluator(g) = ma;
        def run(e, k) = match g(e, a -> k(Ok(a))) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg))
        };
        Evaluator(run)

    pub def empty(): Evaluator[ka, vs, ef, a] = throwError("empty")

    pub def orelse(ma: Evaluator[ka, vs, ef1, a], mb: Evaluator[ka, vs, ef2, a]): Evaluator[ka, vs, ef1 + ef2, a] =
        let Evaluator(g) = ma;
        let Evaluator(h) = mb;
        def run(e, k) = match g(e, k) {
            case Ok(ans)  => Ok(ans)
            case Err(_)   => h(e, k)
        };
        Evaluator(run)


    pub def liftGetter(f: vs -> a \ ef): Evaluator[ka, vs, ef, a]= 
        def run(e, k) = try {
            let ans = f(e);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        Evaluator(run)


    // f should not throw an exception
    pub def liftGetterResult(f: vs -> Result[s, a] \ ef): Evaluator[ka, vs, ef, a] with ToString[s] = 
        def run(e, k) =  match f(e) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        Evaluator(run)


    pub def liftAction(f: Unit -> a \ ef): Evaluator[ka, vs, ef, a] = 
        def run(_, k) = {
            let a = f(); 
            k(a)  
        };
        Evaluator(run)


    pub def liftActionResult(f: Unit -> Result[s, a] \ ef): Evaluator[ka, vs, ef, a] with ToString[s] = 
        def run(_, k) = match f() {
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        Evaluator(run)


}

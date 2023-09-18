/*
 * Copyright 2022 Stephen Tetley
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
    /// The Builder monad is a restricted MutState-Error monad (no direct `put` and `get`).
    /// 
    /// `ka` is the continuation answer type
    ///
    /// Ideally `st` would be `st`: Region -> Type with r: Region but this currently causes a compiler
    /// crash (Flix issue #2113)
    ///
    pub enum Builder[ka: Type, st: Type, _ef: Eff, a: Type](
        st -> (a -> Result[String, ka] \ IO) -> Result[String, ka] \ IO
    )

    instance GradedFunctor[Builder[ka, st]] { 
        pub def map(f: a -> b \ ef1, x: Builder[ka, st, ef, a]): Builder[ka, st, ef + ef1, b] = 
            Graded.Builder.map(f, x)
    }

    instance GradedApplicative[Builder[ka, st]] { 
        pub def point(x: a): Builder[ka, st, ef, a] = 
            Graded.Builder.point(x)

        pub def ap(f: Builder[ka, st, ef1, a -> b \ ef2], 
                    x: Builder[ka, st, ef, a]): Builder[ka, st, ef + ef1 + ef2, b] = 
            Graded.Builder.ap(f, x)
    }

    instance GradedMonad[Builder[ka, st]] { 
        pub def flatMap(k: a -> Builder[ka, st, ef1, b] \ ef, 
                        x: Builder[ka, st, ef2, a]): Builder[ka, st, ef1 + ef2 + ef, b] = 
            Graded.Builder.flatMap(k, x)
    }

    // Orelse not available for Builder 


    instance GradedZero[Builder[ka, st]] { 
        pub def empty(): Builder[ka, st, ef, a] = Graded.Builder.empty()
    }

    instance GradedError[Builder[ka, st]] { 
        pub def throwError(msg: String): Builder[ka, st, ef, a] =
            Graded.Builder.throwError(msg)

        pub def mapError(f: String -> String \ ef1, 
                        ma: Builder[ka, st, ef, a]): Builder[ka, st, ef + ef1, a] = 
            Graded.Builder.mapError(f, ma)

        pub def catchError(ma: Builder[ka, st, ef, a], 
                            hdlr: String -> Builder[ka, st, ef1, a] \ ef2): Builder[ka, st, ef + ef1 + ef2, a] = 
            Graded.Builder.catchError(ma, hdlr)
    
        pub def reifyError(ma: Builder[ka, st, ef, a]): Builder[ka, st, ef, Result[String, a]] = 
            Graded.Builder.reifyError(ma)
    }  


}

mod Graded.Builder {


    use Graded.Builder
    use Graded.Builder.{Builder}


    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runBuilder(ma: Builder[a, st, ef, a], 
                        s: st): Result[String, a] \ ef =
        let Builder(f) = ma;
        let cont = ans -> checked_ecast(Ok(ans));
        unchecked_cast(f(s, cont) as _ \ ef)


    pub def point(x: a): Builder[ka, st, ef, a] = 
        def run(_, k) = k(x);
        Builder(run)


    pub def map(f: a -> b \ ef, ma: Builder[ka, st, ef1, a]): Builder[ka, st, ef + ef1, b] =
        let Builder(g) = ma;
        def run(s, k) = g(s, a -> k(f(a)));
        Builder(run)

    pub def ap(mf: Builder[ka, st, ef1, a -> b \ ef2], ma: Builder[ka, st, ef, a]): Builder[ka, st, ef + ef1 + ef2, b] =
        let Builder(g) = mf;
        let Builder(h) = ma;
        def run(s, k) = g(s, f1 -> h(s, a -> k(f1(a))));
        Builder(run)


    pub def flatMap(f: a -> Builder[ka, st, ef1, b] \ ef2, ma: Builder[ka, st, ef, a]): Builder[ka, st, ef + ef1 + ef2, b] =
        let Builder(g) = ma;
        def run(s, k) = g(s, a -> {let Builder(h) = f(a); h(s, k)});
        Builder(run)


    pub def empty(): Builder[ka, st, ef, a] = 
        throwError("empty")

    pub def throwError(msg: String): Builder[ka, st, ef, a] = 
        def run(_, _) = checked_ecast(Err(msg));
        Builder(run)

    pub def catchError(ma: Builder[ka, st, ef, a], 
                        hdlr: String -> Builder[ka, st, ef1, a] \ ef2): Builder[ka, st, ef + ef1 + ef2, a] = 
        let Builder(g) = ma;
        def run(s, k) = match g(s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let Builder(h) = hdlr(msg); h(s, k)}
        };
        Builder(run)

    pub def mapError(f: String -> String \ ef1, 
                        ma: Builder[ka, st, ef, a]): Builder[ka, st, ef + ef1, a]= 
        let Builder(g) = ma;
        def run(s, k) = match g(s, k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        Builder(run)
    
    pub def reifyError(ma: Builder[ka, st, ef, a]): Builder[ka, st, ef, Result[String, a]] = 
        let Builder(g) = ma;
        def run(s, k) = match g(s, a -> k(Ok(a))) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg))
        };
        Builder(run)

    pub def liftGetter(f: st -> a \ ef): Builder[ka, st, ef, a] = 
        def run(s, k) = try {
            let ans = f(s);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        Builder(run)

    // f should not throw an exception
    pub def liftGetterResult(f: st -> Result[e, a] \ ef): Builder[ka, st, ef, a] with ToString[e] = 
        def run(e, k) =  match f(e) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        Builder(run)

    pub def liftSetter!(f: st -> a \ ef): Builder[ka, st, ef, a] = 
        def run (s, k) = try {
            let a = f(s); 
            k(a)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        Builder(run)

    // f should not throw an exception
    pub def liftSetterResult!(f: st -> Result[e, a] \ ef): Builder[ka, st, ef, a] with ToString[e] = 
        def run(s, k) = match f(s) {
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        Builder(run)


    pub def liftAction(f: Unit -> a \ ef): Builder[ka, st, ef, a] = 
        def run(_, k) = {
            let a = f();
            k(a)
        };
        Builder(run)

    pub def liftActionResult(f: Unit -> Result[e, a] \ ef): Builder[ka, st, ef, a] with ToString[e] = 
        def run(_, k) = match f() {
            case Ok(a)  => k(a)
            case Err(e) => Err(ToString.toString(e))
        };
        Builder(run)

}

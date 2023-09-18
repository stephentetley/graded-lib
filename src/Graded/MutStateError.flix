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
    /// The MutStateError monad is in the codensity style to be stack safe.
    /// 
    /// `ka` is the continuation answer type
    ///
    ///
    /// Ideally st would be st: Region -> Type with r: Region but this currently causes a compiler
    /// crash (Flix issue #2113)
    /// 
    pub enum MutStateError[ka: Type, st: Type, _ef: Eff, a: Type](
        st -> (a -> Result[String, ka] \ IO) -> Result[String, ka] \ IO
    )

    instance GradedFunctor[MutStateError[ka, st]] { 
        pub def map(f: a -> b \ ef1, 
                    x: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef + ef1, b] = 
            Graded.MutStateError.map(f, x)
    }

    instance GradedApplicative[MutStateError[ka, st]] { 
        pub def point(x: a): MutStateError[ka, st, ef, a] = Graded.MutStateError.point(x)

        pub def ap(f: MutStateError[ka, st, ef1, a -> b \ ef2], 
                    x: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef + ef1 + ef2, b] = 
            Graded.MutStateError.ap(f, x)
    }

    instance GradedMonad[MutStateError[ka, st]] { 
        pub def flatMap(k: a -> MutStateError[ka, st, ef1, b] \ ef, 
                        x: MutStateError[ka, st, ef2, a]): MutStateError[ka, st, ef1 + ef2 + ef, b] = 
            Graded.MutStateError.flatMap(k, x)
    }


    instance GradedZero[MutStateError[ka, st]] { 
        pub def empty(): MutStateError[ka, st, ef, a] = Graded.MutStateError.empty()
    }

    instance GradedError[MutStateError[ka, st]] { 
        pub def throwError(msg: String): MutStateError[ka, st, ef, a] =
            Graded.MutStateError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, 
                        ma: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef + ef1, a] = 
            Graded.MutStateError.mapError(f, ma)

        pub def catchError(ma: MutStateError[ka, st, ef, a], 
                            hdlr: String -> MutStateError[ka, st, ef1, a] \ ef2): MutStateError[ka, st, ef + ef1 + ef2, a] = 
            Graded.MutStateError.catchError(ma, hdlr)

        pub def reifyError(ma: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef, Result[String, a]] = 
            Graded.MutStateError.reifyError(ma)
    }  


}

mod Graded.MutStateError {


    use Graded.MutStateError
    use Graded.MutStateError.{MutStateError}


    
    ///
    /// Returns the result of applying `ma` to the state `vs`.
    ///
    pub def runMutStateError(ma: MutStateError[a, st, ef, a], 
                                vs: st): Result[String, a] \ ef =
        let MutStateError(f) = ma;
        let cont = ans -> checked_ecast(Ok(ans));
        unchecked_cast(f(vs, cont) as _ \ ef)


    pub def point(x: a): MutStateError[ka, st, ef, a] = 
        def run(_, k) = k(x);
        MutStateError(run)


    pub def map(f: a -> b \ ef, ma: MutStateError[ka, st, ef1, a]): MutStateError[ka, st, ef + ef1, b] =
        let MutStateError(g) = ma;
        def run(s, k) = g(s, a -> k(f(a)));
        MutStateError(run)

    pub def ap(mf: MutStateError[ka, st, ef1, a -> b \ ef2], ma: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef + ef1 + ef2, b] =
        let MutStateError(g) = mf;
        let MutStateError(h) = ma;
        def run(s, k) = g(s, f1 -> h(s, a -> k(f1(a))));
        MutStateError(run)


    pub def flatMap(f: a -> MutStateError[ka, st, ef1, b] \ ef, ma: MutStateError[ka, st, ef2, a]): MutStateError[ka, st, ef + ef1 + ef2, b] =
        let MutStateError(g) = ma;
        def run(s, k) = g(s, a -> {let MutStateError(h) = f(a); h(s, k)});
        MutStateError(run)


    pub def empty(): MutStateError[ka, st, ef, a] = 
        throwError("empty")

    pub def throwError(msg: String): MutStateError[ka, st, ef, a] = 
        def run(_, _) = checked_ecast(Err(msg));
        MutStateError(run)

    pub def catchError(ma: MutStateError[ka, st, ef, a], 
                        hdlr: String -> MutStateError[ka, st, ef1, a] \ ef2): MutStateError[ka, st, ef + ef1 + ef2, a] = 
        let MutStateError(g) = ma;
        def run(s, k) = match g(s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let MutStateError(h) = hdlr(msg); h(s, k)}
        };
        MutStateError(run)

    pub def mapError(f: String -> String \ ef1, ma: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef + ef1, a] = 
        let MutStateError(g) = ma;
        def run(s, k) = match g(s, k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        MutStateError(run)
    
    pub def reifyError(ma: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef, Result[String, a]] = 
        let MutStateError(g) = ma;
        def run(s, k) = match g(s, a -> k(Ok(a))) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg))
        };
        MutStateError(run)


    /// ideally something like > Err(liftApp(@ \ ef, getMessage, ex)) 
    pub def liftGetter(f: st -> a \ ef): MutStateError[ka, st, ef, a] = 
        def run(s, k) = try {
            let ans = f(s);
            k(ans)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        MutStateError(run)

    // f should not throw an exception
    pub def liftGetterResult(f: st -> Result[e, a] \ ef): MutStateError[ka, st, ef, a] with ToString[e] = 
        def run(e, k) =  match f(e) { 
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        MutStateError(run)

    pub def liftSetter!(f: st -> a \ ef): MutStateError[ka, st, ef, a] = 
        def run (s, k) = try {
            let a = f(s); 
            k(a)
        } catch {
            case ex: ##java.lang.Exception => 
                import java.lang.Throwable.getMessage(): String \ {};
                Err(getMessage(ex))
        };
        MutStateError(run)

    // f should not throw an exception
    pub def liftSetterResult!(f: st -> Result[e, a] \ ef): MutStateError[ka, st, ef, a] with ToString[e] = 
        def run(s, k) = match f(s) {
            case Ok(a)    => k(a)
            case Err(err) => Err(ToString.toString(err))
        };
        MutStateError(run)


    pub def liftAction(f: Unit -> a \ ef): MutStateError[ka, st, ef, a] = 
        def run(_, k) = {
            let a = f();
            k(a)
        };
        MutStateError(run)

    pub def liftActionResult(f: Unit -> Result[e, a] \ ef): MutStateError[ka, st, ef, a] with ToString[e] = 
        def run(_, k) = match f() {
            case Ok(a)  => k(a)
            case Err(e) => Err(ToString.toString(e))
        };
        MutStateError(run)

}

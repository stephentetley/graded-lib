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

namespace Graded {

    ///
    /// State is expected to be unchanged for the extent of an evaluation, 
    /// but it may be mutated outside the Evaluator monad. A `ResultSet` in 
    /// the JDBC library is a typical example. This has operations on the current
    /// row (`getString`, `getTime`, etc.) but also cursor level operations 
    /// to change to another row. An Evaluator for a ResultSet would only provide 
    /// the row operations and be expexcted to run for every row in a traversal
    /// of the results.
    ///
    /// The Evaluation monad is in the codensity style to be stack safe.
    /// 
    /// `ka` is the continuation answer type
    ///
    pub enum Evaluator[ka: Type, st: Type, ef: Bool, a: Type](
        st -> (a -> Result[String, ka] \ ef) -> Result[String, ka] \ ef)

    instance GradedFunctor[Evaluator[ka, st]] { 
        pub def map(f: a -> b \ ef, x: Evaluator[ka, st, ef1, a]): Evaluator[ka, st, ef1 and ef, b] = 
            Graded/Evaluator.map(f, x)
    }

    instance GradedApplicative[Evaluator[ka, st]] { 
        pub def point(x: a): Evaluator[ka, st, true, a] = Graded/Evaluator.point(x)

        pub def ap(f: Evaluator[ka, st, ef1, a -> b \ ef], x: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] = 
            Graded/Evaluator.ap(f, x)
    }

    instance GradedMonad[Evaluator[ka, st]] { 
        pub def flatMap(k: a -> Evaluator[ka, st, ef1, b] \ ef, x: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] = 
            Graded/Evaluator.flatMap(k, x)
    }

    // Orelse available for Evaluator because it is expected to only be reading the state

    instance GradedOr[Evaluator[ka, st]] { 
        pub def orelse(ma: Evaluator[ka, st, ef1, a], mb: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2, a] =
            Graded/Evaluator.orelse(ma, mb)
    }

    instance GradedZero[Evaluator[ka, st]] { 
        pub def empty(): Evaluator[ka, st, ef, a] = Graded/Evaluator.empty()
    }

    instance GradedError[Evaluator[ka, st]] { 
        pub def throwError(msg: String): Evaluator[ka, st, ef, a] =
            Graded/Evaluator.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1, a] = 
            Graded/Evaluator.mapError(f, ma)

        pub def catchError(ma: Evaluator[ka, st, ef, a], hdlr: String -> Evaluator[ka, st, ef1, a] \ ef2): Evaluator[ka, st, ef and ef1 and ef2, a]= 
            Graded/Evaluator.catchError(ma, hdlr)
    }  


}

namespace Graded/Evaluator {


    use Graded.Evaluator
    use Graded.Evaluator.{Evaluator}


    def apply1(ma: Evaluator[ka, st, ef, a], 
                s: st, 
                k: a -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let Evaluator(ma1) = ma;
        ma1(s, k)


    def apply1WithHandler(ma: Evaluator[ka, st, ef, a], 
                            s: st, 
                            k: a -> Result[String, ka] \ ef, 
                            handleK: String -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let Evaluator(ma1) = ma;
        match ma1(s, k) {
            case Err(msg) => handleK(msg)
            case Ok(a)    => Ok(a)
        }

    ///
    /// The first arg is just a proxy - we can use `upcast(identity)` to have it filled in 
    /// by the typechecker.
    /// Ideally we would want something like `liftApp(@ \ ef, getMessage, ex))` - a macro rather than 
    /// a function where we can supply an effect type as the first argument.
    ///
    def liftEff(_: Unit -> Unit \ ef1, ma: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1, a] = 
        unsafe_cast ma as Evaluator[ka, st, ef and ef1, a]

    /// As per liftEff...
    def liftApp(_: Unit -> Unit \ ef1, f: a -> b \ ef, x: a): b \ {ef, ef1} =
        unsafe_cast f(x) as b \ {ef, ef1}

    
    /// Although we can define `liftVal` we should try to avoid it as effects are only a matter for 
    /// function types...
    // def liftVal(_: Unit -> Unit \ ef, x: a): a \ ef = 
    //     unsafe_cast x as a \ ef


    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEvaluator(ma: Evaluator[a, st, ef, a], 
                         s: st): Result[String, a] \ ef =
        let Evaluator(f) = ma;
        let cont = ans -> liftApp(upcast(identity), Ok, ans);
        f(s, cont)


    pub def point(x: a): Evaluator[ka, st, ef, a] = Evaluator((_, k) -> k(x))


    pub def map(f: a -> b \ ef, ma: Evaluator[ka, st, ef1, a]): Evaluator[ka, st, ef1 and ef, b] =
        Evaluator((s, k) ->
            apply1(liftEff(upcast(identity), ma), s, a -> {let b = f(a); k(b)})
        )

    pub def ap(mf: Evaluator[ka, st, ef1, a -> b \ ef], ma: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] =
        Evaluator((s, k) ->
            apply1(liftEff(upcast(identity), mf), s, f1 ->
                apply1(liftEff(upcast(identity),  ma), s, a1 ->
                    k(f1(a1))))
        )


    pub def flatMap(f: a -> Evaluator[ka, st, ef1, b] \ ef, ma: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] =
        Evaluator((s, k) ->
            apply1(liftEff(upcast(identity), ma), s, a ->
                apply1(liftEff(upcast(identity), f(a)), s, b ->
                    k(b)))
        )


    pub def orelse(ma: Evaluator[ka, st, ef1, a], mb: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2, a] =
        Evaluator((s, k) ->
            apply1WithHandler(liftEff(upcast(identity), ma), s, a -> k(a), _ -> apply1(liftEff(upcast(identity), mb), s, b -> k(b)))
        )


    pub def empty(): Evaluator[ka, st, ef, a] = 
        throwError("empty")

    pub def throwError(msg: String): Evaluator[ka, st, ef, a] = 
        liftEff(upcast(identity), Evaluator((_, _) -> Err(msg)))

    pub def mapError(f: String -> String \ ef1, ma: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1, a]= 
        Evaluator((s, k) -> 
            apply1WithHandler(liftEff(upcast(identity), ma), s, a -> k(a), liftApp(upcast(identity), msg -> Err(f(msg))))
        )


    pub def catchError(ma: Evaluator[ka, st, ef, a], 
                        hdlr: String -> Evaluator[ka, st, ef1, a] \ ef2): Evaluator[ka, st, ef and ef1 and ef2, a] = 
        Evaluator((s, k) -> 
            let Evaluator(ma1) = liftEff(upcast(identity), ma);
            match ma1(s, k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => { 
                    let Evaluator(hdlr1) = liftEff(upcast(identity), hdlr(msg)); 
                    hdlr1(s, k)
                }
            }
        )

    /// ideally something like > Err(liftApp(@ \ ef, getMessage, ex)) 
    pub def liftGetter(f: st -> a \ ef): Evaluator[ka, st, ef, a] = 
        Evaluator((s, k) ->
            try {
                let ans = f(s);
                k(ans)
            } catch {
                case ex: ##java.lang.Exception => 
                    import java.lang.Throwable.getMessage(): String \ {};
                    Err(liftApp(upcast(identity), getMessage, ex))
            }            
        )

    // f should not throw an exception
    pub def liftGetterResult(f: st -> Result[e, a] \ ef): Evaluator[ka, st, ef, a] with ToString[e] = 
        Evaluator((s, k) ->
            match f(s) { 
                case Ok(a)  => k(a)
                case Err(e) => Err(ToString.toString(e))
            } 
        )

    pub def liftAction(f: Unit -> a \ ef): Evaluator[ka, st, ef, a] = 
        Evaluator((_, k) ->
            let a = f();
            k(a)
        )

    pub def liftActionResult(f: Unit -> Result[e, a] \ ef): Evaluator[ka, st, ef, a] with ToString[e] = 
        Evaluator((_, k) ->
            match f() {
                case Ok(a)  => k(a)
                case Err(e) => Err(ToString.toString(e))
            }
        )

}

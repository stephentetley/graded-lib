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


namespace Graded {

    ///
    /// Reader-Error like monad where the environment is "read-only mutable state" 
    /// (i.e mutation is expected before or after the Evaluator has run).
    ///
    /// `local` is not supported.
    /// 
    /// `ka` is the continuation answer type
    ///
    /// Ideally st would be st: Region -> Type with r: Region but this ntly causes a compiler
    /// crash (Flix issue #2113)
    ///    
    pub enum Evaluator[ka: Type, st: Type, ef: Bool, a: Type](
        st -> (a -> Result[String, ka] \ ef) -> Result[String, ka] \ ef
    )


    instance GradedFunctor[Evaluator[ka, st]] { 
        pub def map(f: a -> b \ ef1, m: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1, b] = 
            Graded/Evaluator.map(f, m)
    }

    instance GradedApplicative[Evaluator[ka, st]] { 
        pub def point(x: a): Evaluator[ka, st, ef, a] = 
            Graded/Evaluator.point(x)

        pub def ap(f: Evaluator[ka, st, ef1, a -> b \ ef2], m: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1 and ef2, b] = 
            Graded/Evaluator.ap(f, m)
    }

    instance GradedMonad[Evaluator[ka, st]] { 
        pub def flatMap(k: a -> Evaluator[ka, st, ef1, b] \ ef2, m: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1 and ef2, b] = 
            Graded/Evaluator.flatMap(k, m)
    }

    instance GradedZero[Evaluator[ka, st]] { 
        pub def empty(): Evaluator[ka, st, ef, a] = 
            Graded/Evaluator.empty()
    }

    // Orelse available for Evaluator because it is expected to only be reading the state

    instance GradedOr[Evaluator[ka, st]] { 
        pub def orelse(ma: Evaluator[ka, st, ef1, a], mb: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2, a] =
            Graded/Evaluator.orelse(ma, mb)
    }
    
    instance GradedError[Evaluator[ka, st]] { 
        pub def throwError(msg: String): Evaluator[ka, st, ef, a] =
            Graded/Evaluator.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1, a] = 
            Graded/Evaluator.mapError(f, ma)

        pub def catchError(ma: Evaluator[ka, st, ef, a], hdlr: String -> Evaluator[ka, st, ef1, a] \ ef2): Evaluator[ka, st, ef and ef1 and ef2, a] = 
            Graded/Evaluator.catchError(ma, hdlr)
    }  


}

namespace Graded/Evaluator {

    use Graded.Evaluator
    use Graded.Evaluator.{Evaluator}


    ///
    /// Helper function for the implementation of `map` and `ap` etc.
    ///
    def apply1(ma: Evaluator[ka, st, ef, a], 
                e: st, 
                k: a -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let Evaluator(ma1) = ma;
        ma1(e, k)


    def apply1WithHandler(ma: Evaluator[ka, st, ef, a], 
                            e: st,
                            k: a -> Result[String, ka] \ ef, 
                            handleK: String -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let Evaluator(ma1) = ma;
        match ma1(e, k) {
            case Err(msg) => handleK(msg)
            case Ok(a)    => Ok(a)
        }



    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEvaluator(ma: Evaluator[a, st, ef, a], e: st): Result[String, a] \ ef =
        let Evaluator(f) = ma;
        let cont = a -> Graded.liftApp(identity, Ok, a);
        f(e, cont)


    pub def point(x: a): Evaluator[ka, st, ef, a] = 
        Evaluator((_, k) -> k(x))


    pub def map(f: a -> b \ ef1, ma: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1, b] =
        Evaluator((e, k) ->
            apply1(Graded.extendEff(identity, ma), e, a -> k(f(a)))
        )

    pub def ap(mf: Evaluator[ka, st, ef1, a -> b \ ef2], 
                ma: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1 and ef2, b] =
        Evaluator((e, k) ->
            apply1(Graded.extendEff(identity, mf), e, f ->
                apply1(Graded.extendEff(identity, ma), e, a ->
                    k(f(a))))
        )


    pub def flatMap(f: a -> Evaluator[ka, st, ef1, b] \ ef2, 
                    ma: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1 and ef2, b] =
        Evaluator((e, k) ->
            apply1(Graded.extendEff(identity, ma), e, a ->
                apply1(Graded.extendEff(identity, f(a)), e, b ->
                    k(b)))
        )

    pub def throwError(msg: String): Evaluator[ka, st, ef, a] = 
        Evaluator((_, _) -> Graded.liftApp(identity, Err, msg))

    pub def catchError(ma: Evaluator[ka, st, ef, a], 
                        hdlr: String -> Evaluator[ka, st, ef1, a] \ ef2): Evaluator[ka, st, ef and ef1 and ef2, a] = 
        Evaluator((e, k) -> 
            let Evaluator(ma1) = Graded.extendEff(identity, ma);
            match ma1(e, k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => { 
                    let Evaluator(hdlr1) = Graded.extendEff(identity, hdlr(msg)); 
                    hdlr1(e, k)
                }
            }
        )

    pub def mapError(f: String -> String \ ef1, ma: Evaluator[ka, st, ef, a]): Evaluator[ka, st, ef and ef1, a] = 
        Evaluator((e, k) -> 
            apply1WithHandler(Graded.extendEff(identity, ma), e, a -> k(a), Graded.liftApp(identity, msg -> Err(f(msg))))
        )


    pub def empty(): Evaluator[ka, st, ef, a] = throwError("empty")

    pub def orelse(ma: Evaluator[ka, st, ef1, a], mb: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2, a] =
        Evaluator((e, k) ->
            apply1WithHandler(Graded.extendEff(identity, ma), e, a -> k(a), _ -> apply1(Graded.extendEff(identity, mb), e, b -> k(b)))
        )


    pub def liftGetter(f: st -> a \ ef): Evaluator[ka, st, ef, a]= 
        Evaluator((e, k) ->
            try {
                let ans = f(e);
                k(ans)
            } catch {
                case ex: ##java.lang.Exception => 
                    import java.lang.Throwable.getMessage(): String \ {};
                    Err(getMessage(ex))
            }
        )


    // f should not throw an exception
    pub def liftGetterResult(f: st -> Result[e, a] \ ef): Evaluator[ka, st, ef, a] with ToString[e] = 
        Evaluator((e, k) ->
            match f(e) { 
                case Ok(a)    => k(a)
                case Err(err) => Err(ToString.toString(err))
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
                case Ok(a)    => k(a)
                case Err(err) => Err(ToString.toString(err))
            } 
        )

}

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
    /// The Builder monad is a restricted MutState-Error monad (no direct `put` and `get`).
    /// 
    /// `ka` is the continuation answer type
    ///
    /// Ideally st would be st: Region -> Type with r: Region but this ntly causes a compiler
    /// crash (Flix issue #2113)
    ///
    pub enum Builder[ka: Type, st: Type, ef: Bool, a: Type](
        st -> (a -> Result[String, ka] \ ef) -> Result[String, ka] \ ef
    )

    instance GradedFunctor[Builder[ka, st]] { 
        pub def map(f: a -> b \ ef1, x: Builder[ka, st, ef, a]): Builder[ka, st, ef and ef1, b] = 
            Graded/Builder.map(f, x)
    }

    instance GradedApplicative[Builder[ka, st]] { 
        pub def point(x: a): Builder[ka, st, ef, a] = 
            Graded/Builder.point(x)

        pub def ap(f: Builder[ka, st, ef1, a -> b \ ef2], 
                    x: Builder[ka, st, ef, a]): Builder[ka, st, ef and ef1 and ef2, b] = 
            Graded/Builder.ap(f, x)
    }

    instance GradedMonad[Builder[ka, st]] { 
        pub def flatMap(k: a -> Builder[ka, st, ef1, b] \ ef, 
                        x: Builder[ka, st, ef2, a]): Builder[ka, st, ef1 and ef2 and ef, b] = 
            Graded/Builder.flatMap(k, x)
    }

    // Orelse not available for Builder 


    instance GradedZero[Builder[ka, st]] { 
        pub def empty(): Builder[ka, st, ef, a] = Graded/Builder.empty()
    }

    instance GradedError[Builder[ka, st]] { 
        pub def throwError(msg: String): Builder[ka, st, ef, a] =
            Graded/Builder.throwError(msg)

        pub def mapError(f: String -> String \ ef1, 
                        ma: Builder[ka, st, ef, a]): Builder[ka, st, ef and ef1, a] = 
            Graded/Builder.mapError(f, ma)

        pub def catchError(ma: Builder[ka, st, ef, a], 
                            hdlr: String -> Builder[ka, st, ef1, a] \ ef2): Builder[ka, st, ef and ef1 and ef2, a] = 
            Graded/Builder.catchError(ma, hdlr)
    }  


}

namespace Graded/Builder {


    use Graded.Builder
    use Graded.Builder.{Builder}


    def apply1(ma: Builder[ka, st, ef, a], 
                s: st, 
                k: a -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let Builder(ma1) = ma;
        ma1(s, k)


    def apply1WithHandler(ma: Builder[ka, st, ef, a], 
                            s: st, 
                            k: a -> Result[String, ka] \ ef, 
                            handleK: String -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let Builder(ma1) = ma;
        match ma1(s, k) {
            case Err(msg) => handleK(msg)
            case Ok(a)    => Ok(a)
        }



    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runBuilder(ma: Builder[a, st, ef, a], 
                        s: st): Result[String, a] \ ef =
        let Builder(f) = ma;
        let cont = ans -> Graded.liftApp(upcast(identity), Ok, ans);
        f(s, cont)


    pub def point(x: a): Builder[ka, st, ef, a] = 
        Builder((_, k) -> k(x))


    pub def map(f: a -> b \ ef, ma: Builder[ka, st, ef1, a]): Builder[ka, st, ef1 and ef, b] =
        Builder((s, k) ->
            apply1(Graded.extendEff(upcast(identity), ma), s, a -> {let b = f(a); k(b)})
        )

    pub def ap(mf: Builder[ka, st, ef1, a -> b \ ef2], ma: Builder[ka, st, ef, a]): Builder[ka, st, ef and ef1 and ef2, b] =
        Builder((s, k) ->
            apply1(Graded.extendEff(upcast(identity), mf), s, f1 ->
                apply1(Graded.extendEff(upcast(identity),  ma), s, a1 ->
                    k(f1(a1))))
        )


    pub def flatMap(f: a -> Builder[ka, st, ef1, b] \ ef, ma: Builder[ka, st, ef2, a]): Builder[ka, st, ef1 and ef2 and ef, b] =
        Builder((s, k) ->
            apply1(Graded.extendEff(upcast(identity), ma), s, a ->
                apply1(Graded.extendEff(upcast(identity), f(a)), s, b ->
                    k(b)))
        )


    pub def empty(): Builder[ka, st, ef, a] = 
        throwError("empty")

    pub def throwError(msg: String): Builder[ka, st, ef, a] = 
        Builder((_, _) -> Graded.liftApp(upcast(identity), Err, msg))

    pub def mapError(f: String -> String \ ef1, 
                        ma: Builder[ka, st, ef, a]): Builder[ka, st, ef and ef1, a]= 
        Builder((s, k) -> 
            apply1WithHandler(Graded.extendEff(upcast(identity), ma), s, a -> k(a), Graded.liftApp(upcast(identity), msg -> Err(f(msg))))
        )


    pub def catchError(ma: Builder[ka, st, ef, a], 
                        hdlr: String -> Builder[ka, st, ef1, a] \ ef2): Builder[ka, st, ef and ef1 and ef2, a] = 
        Builder((s, k) -> 
            let Builder(ma1) = Graded.extendEff(upcast(identity), ma);
            match ma1(s, k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => { 
                    let Builder(hdlr1) = Graded.extendEff(upcast(identity), hdlr(msg)); 
                    hdlr1(s, k)
                }
            }
        )

    /// ideally something like > Err(liftApp(@ \ ef, getMessage, ex)) 
    pub def liftGetter(f: st -> a \ ef): Builder[ka, st, ef, a] = 
        Builder((s, k) ->
            try {
                let ans = f(s);
                k(ans)
            } catch {
                case ex: ##java.lang.Exception => 
                    import java.lang.Throwable.getMessage(): String \ {};
                    Err(Graded.liftApp(upcast(identity), getMessage, ex))
            }            
        )

    // f should not throw an exception
    pub def liftGetterResult(f: st -> Result[e, a] \ ef): Builder[ka, st, ef, a] with ToString[e] = 
        Builder((s, k) ->
            match f(s) { 
                case Ok(a)  => k(a)
                case Err(e) => Err(ToString.toString(e))
            } 
        )

    pub def liftSetter!(f: st -> a \ ef): Builder[ka, st, ef, a] = 
        Builder((s, k) ->
            try {
                let a = f(s); 
                k(a)
            } catch {
                case ex: ##java.lang.Exception => 
                    import java.lang.Throwable.getMessage(): String \ {};
                    Err(getMessage(ex))
            }            
        )

    // f should not throw an exception
    pub def liftSetterResult!(f: st -> Result[e, a] \ ef): Builder[ka, st, ef, a] with ToString[e] = 
        Builder((s, k) ->
            match f(s) {
                case Ok(a)    => k(a)
                case Err(err) => Err(ToString.toString(err))
            } 
        )


    pub def liftAction(f: Unit -> a \ ef): Builder[ka, st, ef, a] = 
        Builder((_, k) ->
            let a = f();
            k(a)
        )

    pub def liftActionResult(f: Unit -> Result[e, a] \ ef): Builder[ka, st, ef, a] with ToString[e] = 
        Builder((_, k) ->
            match f() {
                case Ok(a)  => k(a)
                case Err(e) => Err(ToString.toString(e))
            }
        )

}

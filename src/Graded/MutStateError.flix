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
    pub enum MutStateError[ka: Type, st: Type, ef: Eff, a: Type](
        st -> (a -> Result[String, ka] \ ef) -> Result[String, ka] \ ef
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
        f(vs, cont)


    pub def point(x: a): MutStateError[ka, st, ef, a] = 
        MutStateError((_, k) -> k(x))


    pub def map(f: a -> b \ ef, ma: MutStateError[ka, st, ef1, a]): MutStateError[ka, st, ef + ef1, b] =
        MutStateError((vs, k) ->
            let MutStateError(maf) = unchecked_cast(ma as MutStateError[ka, st, ef + ef1, a]);
            maf(vs, a -> k(f(a)))
        )

    pub def ap(mf: MutStateError[ka, st, ef1, a -> b \ ef2], ma: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef + ef1 + ef2, b] =
        MutStateError((vs, k) ->
            let MutStateError(mff) = unchecked_cast(mf as MutStateError[ka, st, ef + ef1 + ef2, a -> b \ ef2]);
            let MutStateError(maf) = unchecked_cast(ma as MutStateError[ka, st, ef + ef1 + ef2, a]);
            mff(vs, f ->
                maf(vs, a ->
                    k(f(a))))
        )


    pub def flatMap(f: a -> MutStateError[ka, st, ef1, b] \ ef, ma: MutStateError[ka, st, ef2, a]): MutStateError[ka, st, ef + ef1 + ef2, b] =
        MutStateError((vs, k) ->
            let MutStateError(maf) = unchecked_cast(ma as MutStateError[ka, st, ef + ef1 + ef2, a]);
            maf(vs, a ->
                let MutStateError(faf) = unchecked_cast(f(a) as MutStateError[ka, st, ef + ef1 + ef2, b]);
                faf(vs, b ->
                    k(b)))
        )


    pub def empty(): MutStateError[ka, st, ef, a] = 
        throwError("empty")

    pub def throwError(msg: String): MutStateError[ka, st, ef, a] = 
        MutStateError((_, _) -> checked_ecast(Err(msg)))

    pub def mapError(f: String -> String \ ef1, ma: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef + ef1, a] = 
        MutStateError((vs, k) -> 
            let MutStateError(maf) = unchecked_cast(ma as MutStateError[ka, st, ef + ef1, a]);
            match maf(vs, k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => checked_ecast(Err(f(msg)))
            }
        )
    pub def catchError(ma: MutStateError[ka, st, ef, a], 
                        hdlr: String -> MutStateError[ka, st, ef1, a] \ ef2): MutStateError[ka, st, ef + ef1 + ef2, a] = 
        MutStateError((vs, k) -> 
            let MutStateError(ma1) = unchecked_cast(ma as MutStateError[ka, st, ef + ef1 + ef2, a]);
            match ma1(vs, k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => { 
                    let MutStateError(hdlr1) = unchecked_cast(hdlr(msg) as MutStateError[ka, st, ef + ef1 + ef2, a]); 
                    hdlr1(vs, k)
                }
            }
        )
    
    pub def reifyError(ma: MutStateError[ka, st, ef, a]): MutStateError[ka, st, ef, Result[String, a]] = 
        MutStateError((vs, k) -> 
            let MutStateError(maf) = ma;
            match maf(vs, a -> k(Ok(a))) {
                case Ok(a)    => Ok(a)
                case Err(msg) => k(Err(msg))
            }
        )


    /// ideally something like > Err(liftApp(@ \ ef, getMessage, ex)) 
    pub def liftGetter(f: st -> a \ ef): MutStateError[ka, st, ef, a] = 
        MutStateError((vs, k) ->
            try {
                let ans = f(vs);
                k(ans)
            } catch {
                case ex: ##java.lang.Exception => 
                    import java.lang.Throwable.getMessage(): String \ {};
                    Err(getMessage(ex))
            }            
        )

    // f should not throw an exception
    pub def liftGetterResult(f: st -> Result[e, a] \ ef): MutStateError[ka, st, ef, a] with ToString[e] = 
        MutStateError((vs, k) ->
            match f(vs) { 
                case Ok(a)  => k(a)
                case Err(e) => Err(ToString.toString(e))
            } 
        )

    pub def liftSetter!(f: st -> a \ ef): MutStateError[ka, st, ef, a] = 
        MutStateError((vs, k) ->
            try {
                let a = f(vs); 
                k(a)
            } catch {
                case ex: ##java.lang.Exception => 
                    import java.lang.Throwable.getMessage(): String \ {};
                    Err(getMessage(ex))
            }            
        )

    // f should not throw an exception
    pub def liftSetterResult!(f: st -> Result[e, a] \ ef): MutStateError[ka, st, ef, a] with ToString[e] = 
        MutStateError((vs, k) ->
            match f(vs) {
                case Ok(a)    => k(a)
                case Err(err) => Err(ToString.toString(err))
            } 
        )


    pub def liftAction(f: Unit -> a \ ef): MutStateError[ka, st, ef, a] = 
        MutStateError((_, k) ->
            let a = f();
            k(a)
        )

    pub def liftActionResult(f: Unit -> Result[e, a] \ ef): MutStateError[ka, st, ef, a] with ToString[e] = 
        MutStateError((_, k) ->
            match f() {
                case Ok(a)  => k(a)
                case Err(e) => Err(ToString.toString(e))
            }
        )

}

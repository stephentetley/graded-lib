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
    /// The StateError monad is in the codensity style to be stack safe.
    /// 
    /// `ka` is the continuation answer type
    ///
    pub enum StateError[ka: Type, st: Type, ef: Bool, a: Type](
        st -> (a -> st -> Result[String, ka] \ ef) -> Result[String, ka] \ ef)

    instance GradedFunctor[StateError[ka, st]] { 
        pub def map(f: a -> b \ ef1, m: StateError[ka, st, ef, a]): StateError[ka, st, ef and ef1, b] = 
            Graded.StateError.map(f, m)
    }

    instance GradedApplicative[StateError[ka, st]] { 
        pub def point(x: a): StateError[ka, st, ef, a] = Graded.StateError.point(x)

        pub def ap(f: StateError[ka, st, ef1, a -> b \ ef2], m: StateError[ka, st, ef, a]): StateError[ka, st, ef and ef1 and ef2, b] = 
            Graded.StateError.ap(f, m)
    }

    instance GradedMonad[StateError[ka, st]] { 
        pub def flatMap(k: a -> StateError[ka, st, ef1, b] \ ef2, m: StateError[ka, st, ef, a]): StateError[ka, st, ef and ef1 and ef2, b] = 
            Graded.StateError.flatMap(k, m)
    }

    // Orelse available for StateError because it is expected to only be reading the state

    instance GradedOr[StateError[ka, st]] { 
        pub def orelse(ma: StateError[ka, st, ef1, a], mb: StateError[ka, st, ef2, a]): StateError[ka, st, ef1 and ef2, a] =
            Graded.StateError.orelse(ma, mb)
    }


    instance GradedError[StateError[ka, st]] { 
        pub def throwError(msg: String): StateError[ka, st, ef, a] =
            Graded.StateError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: StateError[ka, st, ef, a]): StateError[ka, st, ef and ef1, a] = 
            Graded.StateError.mapError(f, ma)

        pub def catchError(ma: StateError[ka, st, ef, a], hdlr: String -> StateError[ka, st, ef1, a] \ ef2): StateError[ka, st, ef and ef1 and ef2, a] = 
            Graded.StateError.catchError(ma, hdlr)
        
        pub def reifyError(ma: StateError[ka, st, ef, a]): StateError[ka, st, ef, Result[String, a]] = 
            Graded.StateError.reifyError(ma)    
    }  


}

mod Graded.StateError {


    use Graded.StateError
    use Graded.StateError.{StateError}


    ///
    /// Helper function for the implementation of `map` and `ap` etc.
    ///
    def apply1(ma: StateError[ka, st, ef, a], 
                s: st, 
                k: a -> st -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let StateError(ma1) = ma;
        ma1(s, k)

    def apply1WithHandler(ma: StateError[ka, st, ef, a], 
                            s: st, 
                            k: a -> st -> Result[String, ka] \ ef, 
                            handleK: String -> Result[String, ka] \ ef): Result[String, ka] \ ef =
        let StateError(ma1) = ma;
        match ma1(s, k) {
            case Err(msg) => handleK(msg)
            case Ok(a)    => Ok(a)
        }



    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runStateError(ma: StateError[(st, a), st, ef, a], s: st): Result[String, (st, a)] \ ef =
        let StateError(f) = ma;
        let cont = (a, s1) -> checked_ecast (Ok(s1, a));
        f(s, cont)

    pub def point(x: a): StateError[ka, st, ef, a] = 
        StateError((s, k) -> k(x, s))

    pub def map(f: a -> b \ ef1, ma: StateError[ka, st, ef, a]): StateError[ka, st, ef and ef1, b] =
        StateError((s, k) ->
            apply1(unchecked_cast(ma as StateError[ka, st, ef and ef1, a]), s, (a, s1) -> {let b = f(a); k(b, s1)})
        )

    pub def ap(mf: StateError[ka, st, ef1, a -> b \ ef2], ma: StateError[ka, st, ef, a]): StateError[ka, st, ef and ef1 and ef2, b] =
        StateError((s, k) ->
            apply1(unchecked_cast(mf as StateError[ka, st, ef and ef1 and ef2, a -> b \ ef2]), s, (f, s1) ->
                apply1(unchecked_cast(ma as StateError[ka, st, ef and ef1 and ef2, a]), s1, (a, s2) ->
                    k(f(a), s2)))
        )

    pub def flatMap(f: a -> StateError[ka, st, ef1, b] \ ef2, ma: StateError[ka, st, ef, a]): StateError[ka, st, ef and ef1 and ef2, b] =
        StateError((s, k) ->
            apply1(unchecked_cast(ma as StateError[ka, st, ef and ef1 and ef2, a]), s, (a, s1) ->
                apply1(unchecked_cast(f(a) as StateError[ka, st, ef and ef1 and ef2, b]), s1, (b, s2) ->
                    k(b, s2)))
        )

    pub def orelse(ma: StateError[ka, st, ef1, a], mb: StateError[ka, st, ef2, a]): StateError[ka, st, ef1 and ef2, a] =
        StateError((s, k) ->
            apply1WithHandler(unchecked_cast(ma as StateError[ka, st, ef1 and ef2, a]), s, a ->  k(a), _ -> 
                apply1(unchecked_cast(mb as StateError[ka, st, ef1 and ef2, a]), s, b -> k(b)))
        )

    pub def throwError(msg: String): StateError[r, ka, st, a] = 
        StateError((_, _) -> checked_ecast(Err(msg)))

    pub def catchError(ma: StateError[ka, st, ef, a], 
                        hdlr: String -> StateError[ka, st, ef1, a] \ ef2): StateError[ka, st, ef and ef1 and ef2, a] = 
        StateError((s, k) -> 
            let StateError(ma1) = unchecked_cast(ma as StateError[ka, st, ef and ef1 and ef2, a]);
            match ma1(s, k) {
                case Ok(a)    => Ok(a)
                case Err(msg) => { 
                    let StateError(hdlr1) = unchecked_cast(hdlr(msg) as StateError[ka, st, ef and ef1 and ef2, a]); 
                    hdlr1(s, k)
                }
            }
        )

    pub def mapError(f: String -> String \ ef1, ma: StateError[ka, st, ef, a]): StateError[ka, st, ef and ef1, a] = 
        StateError((s, k) -> 
            apply1WithHandler(unchecked_cast(ma as StateError[ka, st, ef and ef1, a]), s, a -> k(a), msg -> checked_ecast(Err(f(msg))))
        )

    pub def reifyError(ma: StateError[ka, st, ef, a]): StateError[ka, st, ef, Result[String, a]] = 
        StateError((s, k) -> 
            apply1WithHandler(ma, s, a -> k(Ok(a)), msg -> k(Err(msg), s))
        )

    pub def update(f: s -> s \ ef): StateError[ka, s, ef, Unit] = 
        StateError((s, k) -> 
            k((), f(s))
        )
    
    // Pure (true) or polymorphic `ef` ?
    pub def put(st: s): StateError[ka, s, Pure, Unit] = 
        StateError((_, k) -> 
            k((), st)
        )

    // Pure (true) or polymorphic `ef` ?
    pub def get(): StateError[ka, s, Pure, s] = 
        StateError((s, k) -> 
            k(s, s)
        )

    pub def gets(proj: s -> a \ ef): StateError[ka, s, ef, a] = 
        StateError((s, k) -> 
            k(proj(s), s)
        )

}

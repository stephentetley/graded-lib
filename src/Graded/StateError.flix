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
    pub enum StateError[ka: Type, st: Type, _ef: Eff, a: Type](
        st -> (a -> st -> Result[String, ka] \ IO) -> Result[String, ka] \ IO)

    instance GradedFunctor[StateError[ka, st]] { 
        pub def map(f: a -> b \ ef1, m: StateError[ka, st, ef, a]): StateError[ka, st, ef + ef1, b] = 
            Graded.StateError.map(f, m)
    }

    instance GradedApplicative[StateError[ka, st]] { 
        pub def point(x: a): StateError[ka, st, ef, a] = Graded.StateError.point(x)

        pub def ap(f: StateError[ka, st, ef1, a -> b \ ef2], m: StateError[ka, st, ef, a]): StateError[ka, st, ef + ef1 + ef2, b] = 
            Graded.StateError.ap(f, m)
    }

    instance GradedMonad[StateError[ka, st]] { 
        pub def flatMap(k: a -> StateError[ka, st, ef1, b] \ ef2, m: StateError[ka, st, ef, a]): StateError[ka, st, ef + ef1 + ef2, b] = 
            Graded.StateError.flatMap(k, m)
    }

    // Orelse available for StateError because it is expected to only be reading the state

    instance GradedOr[StateError[ka, st]] { 
        pub def orelse(ma: StateError[ka, st, ef1, a], mb: StateError[ka, st, ef2, a]): StateError[ka, st, ef1 + ef2, a] =
            Graded.StateError.orelse(ma, mb)
    }


    instance GradedError[StateError[ka, st]] { 
        pub def throwError(msg: String): StateError[ka, st, ef, a] =
            Graded.StateError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: StateError[ka, st, ef, a]): StateError[ka, st, ef + ef1, a] = 
            Graded.StateError.mapError(f, ma)

        pub def catchError(ma: StateError[ka, st, ef, a], hdlr: String -> StateError[ka, st, ef1, a] \ ef2): StateError[ka, st, ef + ef1 + ef2, a] = 
            Graded.StateError.catchError(ma, hdlr)
        
        pub def reifyError(ma: StateError[ka, st, ef, a]): StateError[ka, st, ef, Result[String, a]] = 
            Graded.StateError.reifyError(ma)    
    }  


}

mod Graded.StateError {


    use Graded.StateError
    use Graded.StateError.{StateError}


    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runStateError(ma: StateError[(st, a), st, ef, a], s: st): Result[String, (st, a)] \ ef =
        let StateError(f) = ma;
        let cont = (a, s1) -> checked_ecast(Ok(s1, a));
        unchecked_cast(f(s, cont) as _ \ ef)

    pub def point(x: a): StateError[ka, st, ef, a] = 
        def run(s, k) = k(x, s);
        StateError(run)

    pub def map(f: a -> b \ ef1, ma: StateError[ka, st, ef, a]): StateError[ka, st, ef + ef1, b] =
        let StateError(g) = ma;
        def run(s, k) = g(s, (a, s1) -> k(f(a), s1));
        StateError(run)


    pub def ap(mf: StateError[ka, st, ef1, a -> b \ ef2], ma: StateError[ka, st, ef, a]): StateError[ka, st, ef + ef1 + ef2, b] =
        let StateError(g) = mf;
        let StateError(h) = ma;
        def run(s, k) = g(s, (f1, s1) -> h(s1, (a, s2) -> k(f1(a), s2)));
        StateError(run)

    pub def flatMap(f: a -> StateError[ka, st, ef1, b] \ ef2, ma: StateError[ka, st, ef, a]): StateError[ka, st, ef + ef1 + ef2, b] =
        let StateError(g) = ma;
        def run(s, k) = g(s, (a, s1) -> {let StateError(h) = f(a); h(s1, k)});
        StateError(run)

    pub def throwError(msg: String): StateError[r, ka, st, a] = 
        def run(_, _) = checked_ecast(Err(msg));
        StateError(run)

    pub def catchError(ma: StateError[ka, st, ef, a], 
                        hdlr: String -> StateError[ka, st, ef1, a] \ ef2): StateError[ka, st, ef + ef1 + ef2, a] = 
        let StateError(g) = ma;
        def run(s, k) = match g(s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let StateError(h) = hdlr(msg); h(s, k)}
        };
        StateError(run)

    pub def mapError(f: String -> String \ ef1, ma: StateError[ka, st, ef, a]): StateError[ka, st, ef + ef1, a] = 
        let StateError(g) = ma;
        def run(s, k) = match g(s, k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        StateError(run)

    pub def reifyError(ma: StateError[ka, st, ef, a]): StateError[ka, st, ef, Result[String, a]] = 
        let StateError(g) = ma;
        def run(s, k) = match g(s, (a, s1) -> k(Ok(a), s1)) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg), s)
        };
        StateError(run)

    pub def orelse(ma: StateError[ka, st, ef1, a], mb: StateError[ka, st, ef2, a]): StateError[ka, st, ef1 + ef2, a] =
        let StateError(g) = ma;
        let StateError(h) = mb;
        def run(s, k) = match g(s, k) {
            case Ok(ans)  => Ok(ans)
            case Err(_)   => h(s, k)
        };
        StateError(run)


    pub def update(f: s -> s \ ef1): StateError[ka, s, ef + ef1, Unit] = 
        def run(s, k) = k((), f(s));
        StateError(run)

    // Pure (true) or polymorphic `ef` ?
    pub def put(st: s): StateError[ka, s, ef, Unit] = 
        def run(_, k) = k((), st);
        StateError(run)

    // Pure (true) or polymorphic `ef` ?
    pub def get(): StateError[ka, s, ef, s] = 
        def run(s, k) = k(s, s);
        StateError(run)

    pub def gets(proj: s -> a \ ef1): StateError[ka, s, ef + ef1, a] = 
        def run(s, k) = k(proj(s), s);
        StateError(run)

}

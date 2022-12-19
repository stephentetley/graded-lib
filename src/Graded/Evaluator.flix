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
        st -> (a -> Result[ka, String] \ ef) -> Result[ka, String] \ ef)

    instance GradedFunctor[Evaluator[ka, st]] { 
        pub def gmap(f: a -> b \ ef, x: Evaluator[ka, st, ef1, a]): Evaluator[ka, st, ef1 and ef, b] = 
            Graded/Evaluator.map(f, x)
    }

    instance GradedApplicative[Evaluator[ka, st]] { 
        pub def gpoint(x: a): Evaluator[ka, st, true, a] = Graded/Evaluator.point(x)

        pub def gap(f: Evaluator[ka, st, ef1, a -> b \ ef], x: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] = 
            Graded/Evaluator.ap(f, x)
    }

    instance GradedMonad[Evaluator[ka, st]] { 
        pub def gflatMap(k: a -> Evaluator[ka, st, ef1, b] \ ef, x: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] = 
            Graded/Evaluator.flatMap(k, x)
    }

}

namespace Graded/Evaluator {


    use Graded.Evaluator
    use Graded.Evaluator.{Evaluator}


    def apply1(ma: Evaluator[ka, st, ef, a], 
                s: st, 
                k: a -> Result[ka, String] \ ef): Result[ka, String] \ ef =
        let Evaluator(ma1) = ma;
        ma1(s, k)



    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runEvaluator(ma: Evaluator[a, st, ef, a], 
                         s: st): Result[a, String] \ ef =
        let Evaluator(f) = ma;
        let cont = a -> unsafe_cast Ok(a) as _ \ ef;
        f(s, cont)


    pub def point(x: a): Evaluator[ka, st, ef, a] = Evaluator((_, k) -> k(x))

    pub def map(f: a -> b \ ef, ma: Evaluator[ka, st, ef1, a]): Evaluator[ka, st, ef1 and ef, b] =
        Evaluator((s, k) ->
            apply1(unsafe_cast ma as Evaluator[ka, st, ef1 and ef, a], s, a -> let b = f(a); k(b))
        )

    pub def ap(mf: Evaluator[ka, st, ef1, a -> b \ ef], ma: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] =
        Evaluator((s, k) ->
            apply1(unsafe_cast mf as Evaluator[ka, st, ef1 and ef2 and ef, a -> b], s, f1 ->
                apply1(unsafe_cast ma as Evaluator[ka, st, ef1 and ef2 and ef, a], s, a1 ->
                    k(f1(a1))))
        )


    pub def flatMap(f: a -> Evaluator[ka, st, ef1, b] \ ef, ma: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] =
        Evaluator((s, k) ->
            apply1(unsafe_cast ma as Evaluator[ka, st, ef1 and ef2 and ef, a], s, a ->
                apply1(unsafe_cast f(a) as Evaluator[ka, st, ef1 and ef2 and ef, b], s, b ->
                    k(b)))
        )

}

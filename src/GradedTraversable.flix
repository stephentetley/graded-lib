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

///
/// An extension of `Traversable` with graded monadic traversals.
///
pub class GradedTraversable[t : Type -> Type] with Traversable[t]{

    ///
    /// Returns the result of applying the graded applicative mapping function `f` to 
    /// all the elements of the data structure `t`.
    ///
    pub def traverse[m: Bool -> Type -> Type, ef: Bool, ef1: Bool, a: Type, b: Type]
                    (f: a -> m[ef, b] \ ef1, t: t[a]): m[ef and ef1, t[b]] with GradedApplicative[m]

    ///
    /// Returns the result of running all the actions in the data structure `t`.
    ///
    pub def sequence[m: Bool -> Type -> Type, ef: Bool, a: Type]
                    (t: t[m[ef, a]]): m[ef, t[a]] with GradedApplicative[m] =
        GradedTraversable.traverse(identity, t)

}


instance GradedTraversable[List] {
    

    pub def traverse[m: Bool -> Type -> Type, ef: Bool, ef1: Bool, a: Type, b: Type]
                    (f: a -> m[ef, b] \ ef1, l: List[a]): m[ef and ef1, List[b]] with GradedApplicative[m] =
        def loop(ll, k) = match ll {
            case Nil     => k(GradedApplicative.point(Nil))
            case x :: xs => loop(xs, ks -> k({let x1 = unchecked_cast(f(x) as m[ef and ef1, b] \ {}); ListHelper.consA(x1, ks)}))
        };       
        loop(l, identity)

}

mod ListHelper {

    pub def consA[m: Bool -> Type -> Type, ef: Bool, ef1: Bool, a: Type]
                (mx: m[ef1, a], ml: m[ef, List[a]]): m[ef and ef1, List[a]] with GradedApplicative[m] =
        use GradedFunctor.{<$>};
        use GradedApplicative.{<*>};
        (((x, xs) -> x :: xs) <$> mx) <*> ml


}
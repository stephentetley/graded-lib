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
/// An extension of `Foldable` with graded monadic traversals.
///
pub class GradedFoldable[t : Type -> Type] with Foldable[t]{

    ///
    /// A graded monadic version of `foldLeft`.
    ///
    /// Applies the graded monadic `f` to a start value `s` and all elements in `t` going
    /// from left to right.
    ///
    pub def foldLeftM[m: Eff -> Type -> Type, ef: Eff, ef1: Eff, a: Type, b: Type]
                        (f: (b, a) -> m[ef, b] \ ef1, s: b, t: t[a]): m[ef + ef1, b] with GradedMonad[m]

    ///
    ///
    /// A graded monadic version of `foldRight`.
    ///
    /// Applies the graded monadic `f` to a start value `s` and all elements in `t` going
    /// from right to left.
    ///
    pub def foldRightM[m: Eff -> Type -> Type, ef: Eff, ef1: Eff, a: Type, b: Type]
                        (f: (a, b) -> m[ef, b] \ ef1, s: b, t: t[a]): m[ef + ef1, b] with GradedMonad[m]

    ///
    /// A graded monadic version of `forEach`.
    ///
    /// Apply `f` to every value in `t`. `f` is applied for its monadic effect,
    /// the answer it produces is discarded.
    ///
    pub def forEachM[m: Eff -> Type -> Type, ef: Eff, ef1: Eff, a: Type, b: Type]
                    (f: a -> m[ef, b] \ ef1, t: t[a]): m[ef + ef1, Unit] with GradedMonad[m] =
        use GradedApplicative.{point, *>};
        GradedFoldable.foldLeftM((acc, a) -> f(a) *> point(acc), (), t)

}


instance GradedFoldable[List] {
    
    pub def foldLeftM[m: Eff -> Type -> Type, ef: Eff, ef1: Eff, a: Type, b: Type]
                    (f: (b, a) -> m[ef, b] \ ef1, s: b, l: List[a]): m[ef + ef1, b] with GradedMonad[m] = 
        def loop(ll, acc) = match ll {
            case Nil     => acc
            case x :: rs => {let ms1 = GradedMonad.flatMap(y -> f(y, x), acc); loop(rs, ms1)}
        };
        loop(l, GradedApplicative.point(s))

    pub def foldRightM[m: Eff -> Type -> Type, ef: Eff, ef1: Eff, a: Type, b: Type]
                        (f: (a, b) -> m[ef, b] \ ef1, s: b, l: List[a]): m[ef + ef1, b] with GradedMonad[m] =
        def loop(ll, k) = match ll {
            case Nil     => k(GradedApplicative.point(s))
            case x :: rs => loop(rs, s1 -> k(GradedMonad.flatMap(y -> f(x, y), s1)))
        };
        loop(l, identity)

}
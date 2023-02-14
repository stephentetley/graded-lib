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


pub class GradedOr[m: Bool -> Type -> Type] with GradedMonad[m] {

    ///
    /// "Left catch" / left biased choice
    ///
    pub def orelse(a: m[ef1, a], b: m[ef2, a]): m[ef1 and ef2, a]

}

namespace GradedOr {

    use GradedFunctor.{<$>}

    pub def <|>[a: Type, ef1: Bool, ef2: Bool, m: Bool -> Type -> Type]
                (a: m[ef1, a], b: m[ef2, a]): m[ef1 and ef2, a] with GradedOr[m] = orelse(a, b)

    pub def optional[a: Type, ef: Bool, m: Bool -> Type -> Type]
                    (ma: m[ef, a]): m[ef, Option[a]] with GradedOr[m] = 
        orelse(Some <$> ma, GradedApplicative.point(None))

    pub def withDefault[a: Type, ef: Bool, m: Bool -> Type -> Type]
                       (d: a, x: m[ef, a]): m[ef, a] with GradedOr[m] =
        orelse(x, GradedApplicative.point(d))

}

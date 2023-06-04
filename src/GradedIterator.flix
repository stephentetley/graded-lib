/*
 * Copyright 2020 Stephen Tetley
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


mod GradedIterator {
    
    use GradedApplicative.{point}
    use GradedMonad.{>>=}

    use Iterator.Iterator
    use Iterator.Step.{Ans, Skip, Done}
    
    ///
    /// Applies `f` to a start value `s` and all elements in `iter` going from left to right.
    ///
    /// That is, the result is of the form: `f(...f(f(s, x1), x2)..., xn)`.
    ///
    /// Consumes the entire iterator.
    ///
    pub def foldLeftM[a: Type, b: Type, ef: Eff, ef1: Eff, ef2: Eff, m: Eff -> Type -> Type, r: Region]
                    (f: (b, a) -> m[ef1, b] \ ef2, s: b, iter: Iterator[a, ef, r]): m[ef + ef1 + ef2 + r, b] \ {ef, r} with GradedMonad[m]=
        let Iterator(_, iterF) = iter;
        let f1 = (acc, x) -> unchecked_cast(f(acc, x) as m[ef + ef1 + ef2 + r, b]);
        def loop(macc) = match iterF() {
            case Skip   => loop(macc)
            case Ans(a) => loop(macc >>= acc -> f1(acc, a))
            case Done   => macc
        };
        loop(point(s))
}

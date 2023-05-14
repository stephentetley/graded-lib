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
    /// Just a Codensity monad graded with an effect
    ///
    pub enum Codensity[ka: Type, ef: Eff, a: Type](
        (a -> ka \ ef) -> ka \ ef)

    instance GradedFunctor[Codensity[ka]] { 
        pub def map(f: a -> b \ ef1, m: Codensity[ka, ef, a]): Codensity[ka, ef + ef1, b] = 
            Graded.Codensity.map(f, m)
    }

    instance GradedApplicative[Codensity[ka]] { 
        pub def point(x: a): Codensity[ka, ef, a] = Graded.Codensity.point(x)

        pub def ap(f: Codensity[ka, ef1, a -> b \ ef2], m: Codensity[ka, ef, a]): Codensity[ka, ef + ef1 + ef2, b] = 
            Graded.Codensity.ap(f, m)
    }

    instance GradedMonad[Codensity[ka]] { 
        pub def flatMap(k: a -> Codensity[ka, ef1, b] \ ef2, m: Codensity[ka, ef, a]): Codensity[ka, ef + ef1 + ef2, b] = 
            Graded.Codensity.flatMap(k, m)
    }


}

mod Graded.Codensity {


    use Graded.Codensity
    use Graded.Codensity.{Codensity}


    ///
    /// Helper function for the implementation of `map` and `ap` etc.
    ///
    def apply1(ma: Codensity[ka, ef, a], k: a -> ka \ ef): ka \ ef =
        let Codensity(ma1) = ma;
        ma1(k)


    ///
    /// Run Codensity
    ///
    pub def runCodensity(ma: Codensity[a, ef, a]): a \ ef =
        let Codensity(f) = ma;
        let cont = a -> checked_ecast(a);
        f(cont)

    pub def point(x: a): Codensity[ka, ef, a] = 
        Codensity(k -> k(x))

    pub def map(f: a -> b \ ef, ma: Codensity[ka, ef1, a]): Codensity[ka, ef1 + ef, b] =
        Codensity(k ->
            apply1(unchecked_cast(ma as Codensity[ka, ef1 + ef, a]), a -> {let b = f(a); k(b)})
        )

    pub def ap(mf: Codensity[ka, ef1, a -> b \ ef2], ma: Codensity[ka, ef, a]): Codensity[ka, ef + ef1 + ef2, b] =
        Codensity(k ->
            apply1(unchecked_cast(mf as Codensity[ka, ef + ef1 + ef2, a -> b \ ef2]), f ->
                apply1(unchecked_cast(ma as Codensity[ka, ef + ef1 + ef2, a]), a ->
                    k(f(a))))
        )

    pub def flatMap(f: a -> Codensity[ka, ef1, b] \ ef2, ma: Codensity[ka, ef, a]): Codensity[ka, ef + ef1 + ef2, b] =
        Codensity(k ->
            apply1(unchecked_cast(ma as Codensity[ka, ef + ef1 + ef2, a]), a ->
                apply1(unchecked_cast(f(a) as Codensity[ka, ef + ef1 + ef2, b]), b ->
                    k(b)))
        )


}

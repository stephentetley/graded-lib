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
    pub enum Codensity[ka: Type, _ef: Eff, a: Type](
        (a -> ka \ IO) -> ka \ IO)

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
    /// Run Codensity
    ///
    pub def runCodensity(ma: Codensity[a, ef, a]): a \ ef =
        let Codensity(f) = ma;
        let cont = a -> unchecked_cast(a as _ \ IO);
        unchecked_cast(f(cont) as _ \ ef)

    pub def point(x: a): Codensity[ka, ef, a] = 
        Codensity(k -> k(x))

    pub def map(f: a -> b \ ef, ma: Codensity[ka, ef1, a]): Codensity[ka, ef1 + ef, b] =
        let Codensity(g) = ma;
        def run(k) = g(a -> {let b = unchecked_cast(f(a) as _ \ IO); k(b)});
        Codensity(run)

    pub def ap(mf: Codensity[ka, ef1, a -> b \ ef2], ma: Codensity[ka, ef, a]): Codensity[ka, ef + ef1 + ef2, b] =
        flatMap(f -> flatMap(a -> point(f(a)), ma), mf)

    pub def flatMap(f: a -> Codensity[ka, ef1, b] \ ef2, ma: Codensity[ka, ef, a]): Codensity[ka, ef + ef1 + ef2, b] =
        let Codensity(g) = ma;
        def run(k) = g(a -> {let Codensity(h) = unchecked_cast(f(a) as _ \ IO); h(b -> k(b))});
        Codensity(run)

    pub def liftEffect(f: Unit -> a \ ef): Codensity[ka, ef, a] = 
        Codensity(k -> k(f()))

}

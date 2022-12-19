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


    /// `ka` is the continuation answer type
    ///
    pub enum Cont[ka: Type, ef: Bool, a: Type]((a -> ka \ ef) -> ka \ ef)

    // instance GradedFunctor[Evaluator[ka, st]] { 
    //     pub def gmap(f: a -> b \ ef, x: Evaluator[ka, st, ef1, a]): Evaluator[ka, st, ef1 and ef, b] = 
    //         Graded/Evaluator.map(f, x)
    // }

    // instance GradedApplicative[Evaluator[ka, st]] { 
    //     pub def gpoint(x: a): Evaluator[ka, st, true, a] = Graded/Evaluator.point(x)

    //     pub def gap(f: Evaluator[ka, st, ef1, a -> b \ ef], x: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] = 
    //         Graded/Evaluator.ap(f, x)
    // }

    // instance GradedMonad[Evaluator[ka, st]] { 
    //     pub def gflatMap(k: a -> Evaluator[ka, st, ef1, b] \ ef, x: Evaluator[ka, st, ef2, a]): Evaluator[ka, st, ef1 and ef2 and ef, b] = 
    //         Graded/Evaluator.flatMap(k, x)
    // }

}

namespace Graded/Cont {


    use Graded.Cont
    use Graded.Cont.{Cont}


    def getCont(ma: Cont[ka, ef, a], k: a -> ka \ ef): ka \ ef =
        let Cont(ma1) = ma;
        ma1(k)

    pub def point(x: a): Cont[ka, ef, a] = Cont(k -> k(x))

    pub def gflatMap0(f: a -> Cont[ka, ef1, b], ma: Cont[ka, ef1, a]): Cont[ka, ef1, b] = 
        Cont(k -> 
            getCont(ma, a -> getCont(f(a), k))
        )


    def getContX(ma: Cont[ka, ef1, a], k: a -> ka \ ef): ka & ef1 and ef =
        let Cont(ma1) = unsafe_cast ma as Cont[ka, ef1 and ef, a];
        let k1 = a -> unsafe_cast k(a) as _ & (ef1 and ef);
        ma1(k1)

    pub def gflatMap(f: a -> Cont[ka, ef1, b], ma: Cont[ka, ef2, a]): Cont[ka, ef1 and ef2, b] = 
        Cont(k -> 
            getContX(ma, a -> getContX(f(a), k))
        )


}

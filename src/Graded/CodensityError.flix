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
    /// Codensity (CPS) / Error monad.
    /// 
    /// `ka` is the continuation answer type
    ///
    pub enum CodensityError[ka: Type, _ef: Eff, a: Type](
        (a -> Result[String, ka] \ IO) -> Result[String, ka] \ IO)

    instance GradedFunctor[CodensityError[ka]] { 
        pub def map(f: a -> b \ ef1, m: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1, b] = 
            Graded.CodensityError.map(f, m)
    }

    instance GradedApplicative[CodensityError[ka]] { 
        pub def point(x: a): CodensityError[ka, ef, a] = 
            Graded.CodensityError.point(x)

        pub def ap(f: CodensityError[ka, ef1, a -> b \ ef2], m: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1 + ef2, b] = 
            Graded.CodensityError.ap(f, m)
    }

    instance GradedMonad[CodensityError[ka]] { 
        pub def flatMap(k: a -> CodensityError[ka, ef1, b] \ ef2, m: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1 + ef2, b] = 
            Graded.CodensityError.flatMap(k, m)
    }

    instance GradedZero[CodensityError[ka]] { 
        pub def empty(): CodensityError[ka, ef, a] = 
            Graded.CodensityError.empty()
    }

    // Orelse available for Evaluator because it is expected to only be reading the state

    instance GradedOr[CodensityError[ka]] { 
        pub def orelse(ma: CodensityError[ka, ef1, a], mb: CodensityError[ka, ef2, a]): CodensityError[ka, ef1 + ef2, a] =
            Graded.CodensityError.orelse(ma, mb)
    }
    
    instance GradedError[CodensityError[ka]] { 
        pub def throwError(msg: String): CodensityError[ka, ef, a] =
            Graded.CodensityError.throwError(msg)

        pub def mapError(f: String -> String \ ef1, ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1, a] = 
            Graded.CodensityError.mapError(f, ma)

        pub def catchError(ma: CodensityError[ka, ef, a], hdlr: String -> CodensityError[ka, ef1, a] \ ef2): CodensityError[ka, ef + ef1 + ef2, a] = 
            Graded.CodensityError.catchError(ma, hdlr)

        pub def reifyError(ma: CodensityError[ka, ef, a]): CodensityError[ka, ef, Result[String, a]] = 
            Graded.CodensityError.reifyError(ma)            
    }  


}

mod Graded.CodensityError {

    use Graded.CodensityError
    use Graded.CodensityError.{CodensityError}


    ///
    /// Returns the result of applying `ma` to the state `s`.
    ///
    pub def runCodensityError(ma: CodensityError[a, ef, a]): Result[String, a] \ ef =
        let CodensityError(f) = ma;
        let cont = a -> checked_ecast(Ok(a));
        unchecked_cast(f(cont) as _ \ ef)


    pub def point(x: a): CodensityError[ka, ef, a] = 
        def run(k) = k(x);
        CodensityError(run)

    pub def map(f: a -> b \ ef1, ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1, b] =
        let CodensityError(g) = ma;
        def run(k) = g(a -> k(f(a)));
        CodensityError(run)

    pub def ap(mf: CodensityError[ka, ef1, a -> b \ ef2], ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1 + ef2, b] =
        let CodensityError(g) = mf;
        let CodensityError(h) = ma;
        def run(k) = g(f1 -> h(a -> k(f1(a))));
        CodensityError(run)

    pub def flatMap(f: a -> CodensityError[ka, ef1, b] \ ef2, ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1 + ef2, b] =
        let CodensityError(g) = ma;
        def run(k) = g(a -> {let CodensityError(h) = f(a); h(k)});
        CodensityError(run)

    pub def throwError(msg: String): CodensityError[ka, ef, a] = 
        def run(_) = checked_ecast(Err(msg));
        CodensityError(run)

    pub def catchError(ma: CodensityError[ka, ef, a], 
                        hdlr: String -> CodensityError[ka, ef1, a] \ ef2): CodensityError[ka, ef + ef1 + ef2, a] = 
        let CodensityError(g) = ma;
        def run(k) = match g(k) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => {let CodensityError(h) = hdlr(msg); h(k)}
        };
        CodensityError(run)


    pub def mapError(f: String -> String \ ef1, ma: CodensityError[ka, ef, a]): CodensityError[ka, ef + ef1, a] = 
        let CodensityError(g) = ma;
        def run(k) = match g(k) {
            case Ok(a)    => Ok(a)
            case Err(msg) => Err(f(msg))
        };
        CodensityError(run)


    pub def reifyError(ma: CodensityError[ka, ef, a]): CodensityError[ka, ef, Result[String, a]] = 
        let CodensityError(g) = ma;
        def run(k) = match g(a -> k(Ok(a))) {
            case Ok(ans)  => Ok(ans)
            case Err(msg) => k(Err(msg))
        };
        CodensityError(run)

    pub def empty(): CodensityError[ka, ef, a] = throwError("empty")

    pub def orelse(ma: CodensityError[ka, ef1, a], mb: CodensityError[ka, ef2, a]): CodensityError[ka, ef1 + ef2, a] =
        let CodensityError(g) = ma;
        let CodensityError(h) = mb;
        def run(k) = match g(k) {
            case Ok(ans)  => Ok(ans)
            case Err(_)   => h(k)
        };
        CodensityError(run)


    pub def liftAction(f: Unit -> a \ ef): CodensityError[ka, ef, a] = 
        def run(k) = k(f());
        CodensityError(run)

    pub def liftActionResult(f: Unit -> Result[String, a] \ ef): CodensityError[ka, ef, a] = 
        def run(k) = match f() { 
            case Ok(a)    => k(a)
            case Err(msg) => Err(msg)
        };
        CodensityError(run)

}

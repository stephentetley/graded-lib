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

/// Catching the Error does not imply that any state is
/// reset, but it does allow recovery from failure.
/// 
/// Error type is fixed to string - this could change if/when Flix gets MPTCs.
///
pub class GradedError[m: Bool -> Type -> Type] with GradedMonad[m] {
    
    pub def throwError(e: String): m[ef, a]

    pub def mapError(f: String -> String \ ef1, m: m[ef, a]): m[ef and ef1, a]

    pub def catchError(m: m[ef, a], hdl: String -> m[ef1, a] \ ef2): m[ef and ef1 and ef2, a]

}

namespace GradedError {

    use GradedApplicative.point;
    

    pub def swapError[m: Bool -> Type -> Type, ef: Bool, a: Type]
                        (msg: String, ma: m[ef, a]): m[ef, a] with GradedError[m] = 
        GradedError.mapError(_ -> msg, ma)

    pub def liftOption[m: Bool -> Type -> Type, ef: Bool, err: Type, a: Type]
                        (e: err, x: Option[a]): m[ef, a] with GradedError[m], ToString[err] = match x { 
        case Some(x1) => point(x1)
        case None     => GradedError.throwError(ToString.toString(e))
    }

    pub def liftResult[m: Bool -> Type -> Type, ef: Bool, err: Type, a: Type]
                        (x: Result[err, a]): m[ef, a] with GradedError[m], ToString[err] = match x { 
        case Ok(x1)   => point(x1)
        case Err(msg) => GradedError.throwError(ToString.toString(msg))
    }

    pub def guard[m: Bool -> Type -> Type, ef: Bool]
                    (x: Bool): m[ef, Unit] with GradedError[m] = match x { 
        case true  => point()
        case false => throwError("guard")
    }


}


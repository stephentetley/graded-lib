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

namespace Graded {

    ///
    /// Capture an "ambient" effect within the constructor `m`
    ///
    pub def captureEff[m: Bool -> Type -> Type, ef: Bool, ef1: Bool, a: Type]
                        (f: Unit -> m[ef, a] \ ef1): m[ef and ef1, a] = 
        unsafe_cast f() as m[ef and ef1, a] \ {}

    ///
    /// The first arg is just a proxy - we can use `upcast(identity)` to have it filled in 
    /// by the typechecker.
    /// Ideally we would want something like `liftApp(@ \ ef, getMessage, ex))` - a macro rather than 
    /// a function where we can supply an effect type as the first argument.
    ///
    pub def extendEff[m: Bool -> Type -> Type, ef: Bool, ef1: Bool, a: Type]
                        (_: Unit -> Unit \ ef1, ma: m[ef, a]): m[ef and ef1, a] = 
        unsafe_cast ma as m[ef and ef1, a]

    /// As per Graded.extendEff...
    pub def liftApp(_: Unit -> Unit \ ef1, f: a -> b \ ef, x: a): b \ {ef, ef1} =
        unsafe_cast f(x) as b \ {ef, ef1}


}
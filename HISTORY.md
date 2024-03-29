### v0.9.0
   Renamed `liftEffect` to `liftAction` in `CodensityError` and `Codensity`.

### v0.8.0
   Rewrote all graded monads to use `IO` internally to avoid a casting bug that caused runtime failures.

### v0.7.0
   Inlined and eliminated `apply...` functions.
   Added `when...` family of functions.

### v0.6.1
   Added `RgnEnvEvaluator` and `GradedIterator`.

### v0.6.0
   Updated to use new effect syntax naming (`+` rather than `and`, `Eff` rather than `Bool`).

### v0.5.0
   Added EnvEvaluator.
   Naming changes for Reader operations `askEnv` becomes `ask`, `localEnv` becomes `local` etc.
   Generalized effect types of `update`, `gets`, etc.

### v0.4.0
   Added `reifyError` to `GradedError` class.

### v0.3.1
   Added EnvStateError.
   Changed to use dot as namespace sparator.

### v0.3.0
   Changed to `mod` rather than `namespace`.

### v0.2.0
   Added Codensity and CodensityError.
   Removed Graded (use Flix casts directly instead).

### v0.1.0
   Initial release.

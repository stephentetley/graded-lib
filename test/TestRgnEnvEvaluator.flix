
mod TestRgnEnvEvaluator {

    use Graded.RgnEnvEvaluator
    use Graded.RgnEnvEvaluator.{runRgnEnvEvaluator}
    use GradedApplicative.{point}

    @test
    def test01(): Bool = region rc {
        let st = Array#{} @ rc;
        runRgnEnvEvaluator(point(5), rc, {start = 1}, st) == Ok(5)
    }

    @test
    def test02(): Bool = region rc {
        use GradedFunctor.{<$$>};
        let st = Array#{} @ rc;
        runRgnEnvEvaluator(point(5) <$$> (x -> x + 5), rc, {start = 1}, st) == Ok(10)
    }

    @test
    def test03(): Bool = region rc {
        let st = Array#{} @ rc;
        runRgnEnvEvaluator(GradedMonad.flatMap(x -> point(x + 5), point(5)), rc, {start = 1}, st) == Ok(10)
    }

    @test
    def test04(): Bool =  region rc {
        use GradedApplicative.{*>};
        let st = Array#{} @ rc;
        runRgnEnvEvaluator(RgnEnvEvaluator.throwError("Crash") *> point(5), rc, {start = 1}, st) == Err("Crash")
    }

    @test
    def test05(): Bool \ IO = region rc {
        use GradedApplicative.{*>};
        let st = Array#{} @ rc;
        runRgnEnvEvaluator(RgnEnvEvaluator.liftAction(_ -> println("No Crash")), rc, {start = 1}, st) == Ok()
    }

    @test
    def test06(): Bool = region rc {
        use GradedApplicative.{*>};
        let st = Array#{} @ rc;
        runRgnEnvEvaluator(RgnEnvEvaluator.mapError(_ -> "Bad", RgnEnvEvaluator.throwError("Crash") *> point(5)), rc, {start = 1}, st) == Err("Bad")
    }

   @test
    def test07(): Bool = region rc {
        let st = Array#{} @ rc;
        let ans: Result[String, Result[String, Int32]] = Ok(Err("Crash"));
        runRgnEnvEvaluator(RgnEnvEvaluator.reifyError(RgnEnvEvaluator.throwError("Crash")), rc, {start = 1}, st) == ans
    }

}

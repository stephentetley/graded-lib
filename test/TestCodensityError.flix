
mod TestCodensityError {

    use Graded.CodensityError
    use Graded.CodensityError.{runCodensityError}
    use GradedApplicative.{point}

    @test
    def test01(): Bool = 
        runCodensityError(point(5)) == Ok(5)

    @test
    def test02(): Bool = 
        use GradedFunctor.{<$$>};
        runCodensityError(point(5) <$$> (x -> x + 5)) == Ok(10)

    @test
    def test03(): Bool = 
        runCodensityError(GradedMonad.flatMap(x -> point(x + 5), point(5))) == Ok(10)

    @test
    def test04(): Bool = 
        use GradedApplicative.{*>};
        runCodensityError(CodensityError.throwError("Crash") *> point(5)) == Err("Crash")


    @test
    def test05(): Bool \ IO = 
        use GradedApplicative.{*>};
        runCodensityError(CodensityError.liftAction(_ -> println("No Crash"))) == Ok()


    @test
    def test06(): Bool = 
        use GradedApplicative.{*>};
        runCodensityError(CodensityError.mapError(_ -> "Bad", CodensityError.throwError("Crash") *> point(5))) == Err("Bad")

    // pub def output(msg: String): CodensityError[ka, IO, Unit] = 
    //     CodensityError.liftAction(_ -> println(msg))

    // @test
    // def test06(): Bool \ IO = 
    //     use GradedApplicative.{*>};
    //     runCodensityError(CodensityError.liftAction(_ -> println("No Crash")) *> Graded.CodensityError.point(5)) == Ok(5)


    // /// Fix an effect in a graded monad - get a regular monad (well we would if IOError was an enum...).
    // ///
    // /// However, this result is not very remarkable: fixing to a known set of effects is not a good
    // /// strategy for a library writer, we would not want to prevent e.g. a user returning arrays from 
    // /// a Parser monad so the effect should always be open.
    // type alias IOError[ka: Type, a: Type] = CodensityError[ka, IO, a]

    
    // pub def runIOError(ma: IOError[a, a]): Result[String, a] \ IO = 
    //     runCodensityError(ma)

    // pub def output(msg: String): IOError[ka, Unit] = 
    //     CodensityError.liftAction(_ -> println(msg))


    // @test
    // def test05(): Bool \ IO = 
    //     use GradedApplicative.{*>};
    //     runIOError(output("No crash") *> Graded.CodensityError.point(5)) == Ok(5)

    @test
    def test07(): Bool = 
        let ans: Result[String, Result[String, Int32]] = Ok(Err("Crash"));
        runCodensityError(CodensityError.reifyError(CodensityError.throwError("Crash"))) == ans

}
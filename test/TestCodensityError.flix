
namespace TestCodensityError {

    use Graded.CodensityError
    use Graded/CodensityError.{runCodensityError}
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


    /// Fix an effect in a graded monad - get a regular monad (well we would if IOError was an enum...)
    type alias IOError[ka: Type, a: Type] = CodensityError[ka, Impure, a]

    
    pub def runIOError(ma: IOError[a, a]): Result[String, a] \ IO = 
        runCodensityError(ma)

    pub def output(msg: String): IOError[ka, Unit] = 
        CodensityError.liftEff(_ -> println(msg))


    @test
    def test05(): Bool \ IO = 
        use GradedApplicative.{*>};
        runIOError(output("No crash") *> point(5)) == Ok(5)

}
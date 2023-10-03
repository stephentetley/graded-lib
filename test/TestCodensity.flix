
mod TestCodensity {

    use Graded.Codensity.{runCodensity}
    use GradedApplicative.{point}

    @test
    def test01(): Bool = 
        runCodensity(point(5)) == 5

    @test
    def test02(): Bool = 
        use GradedFunctor.{<$$>};
        runCodensity(point(5) <$$> (x -> x + 5)) == 10
    
    @test
    def test02b(): Bool \ IO = 
        use GradedFunctor.{map};
        runCodensity(map(x -> {println("was: ${x}"); x + 5}, point(5))) == 10

    @test
    def test03(): Bool = 
        runCodensity(GradedMonad.flatMap(x -> point(x + 5), point(5))) == 10

    @test
    def test05(): Bool \ IO = 
        use GradedApplicative.{*>};
        runCodensity(Graded.Codensity.liftAction(_ -> println("No Crash"))) == ()

    @test
    def test06(): Bool \ IO = 
        use GradedApplicative.{*>};
        runCodensity(Graded.Codensity.liftAction(_ -> println("No Crash")) *> Graded.Codensity.point(5)) == 5

}
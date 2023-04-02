
namespace TestCodensity {

    use Graded/Codensity.{runCodensity}
    use GradedApplicative.{point}

    @test
    def test01(): Bool = 
        runCodensity(point(5)) == 5

    @test
    def test02(): Bool = 
        use GradedFunctor.{<$$>};
        runCodensity(point(5) <$$> (x -> x + 5)) == 10

    @test
    def test03(): Bool = 
        runCodensity(GradedMonad.flatMap(x -> point(x + 5), point(5))) == 10


}
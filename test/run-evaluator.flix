// java -jar ..\bin\flix-master.jar .\test\run-graded-error.flix .\src\*.flix .\src\Graded\*.flix

pub def main(): Int32 \ IO = 
    println("run-graded-error...");
    test01();
    test02();
    test03();
    0


pub def test01(): Unit \ IO = 
    use GradedApplicative.{point};
    println("test01");
    Graded/Evaluator.runEvaluator(point(5), 0) |> println

pub def test02(): Unit \ IO = 
    use GradedApplicative.{point};
    use GradedError.{catchError, throwError};
    println("test02");
    Graded/Evaluator.runEvaluator(catchError(throwError("blowup"), _msg -> point(1000)), 0) |> println    

pub def test03(): Unit \ IO = 
    use GradedApplicative.{point};
    use GradedError.{throwError};
    println("test03");
    Graded/Evaluator.runEvaluator(GradedApplicative.productRight(throwError("blowup"), point(5)), 0) |> println

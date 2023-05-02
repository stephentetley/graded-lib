// java -jar ..\bin\flix-master.jar .\temp\run-state-error.flix .\src\*.flix .\src\Graded\StateError.flix

use Graded.StateError

pub def main(): Int32 \ IO = 
    println("run-state-error...");
    test01();
    test02();
    0


pub def test01(): Unit \ IO = 
    use GradedApplicative.{point};
    println("test01");
    Graded.StateError.runStateError(point(5), 0) |> println

pub def test02(): Unit \ IO = 
    use GradedApplicative.{point};
    use GradedError.{catchError, throwError};
    println("test02");
    Graded.StateError.runStateError(action02(), 0) |> println    

// pub def action02(): StateError[ka, Int32, Pure, (Int32, Int32)] = 
//     use Graded.StateError.{flatMap, get, put};
//     use GradedApplicative.{point};
//     forM(i <- get();
//         put(i + 10);
//         j <- get())
//     yield ((i, j))


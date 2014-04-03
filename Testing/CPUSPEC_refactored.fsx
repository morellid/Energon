open System
open System.Text
open System.Collections
open System.Collections.Generic

#I @"C:\Users\davidemorelli\Documents\GitHub\Energon\packages\MathNet.Numerics.FSharp.2.6.0\lib\net40"
#I @"C:\Users\davidemorelli\Documents\GitHub\Energon\packages\MathNet.Numerics.2.6.2\lib\net40"
#r "MathNet.Numerics.FSharp.dll"
#r "MathNet.Numerics.dll"
 
open MathNet.Numerics
open MathNet.Numerics.LinearAlgebra.Double
open MathNet.Numerics.Distributions
open MathNet.Numerics.Statistics

#r @"C:\Users\davidemorelli\Documents\GitHub\Energon\Solvers\bin\Debug\Solvers.dll"

let folder = @"C:\Data\"    


let r = new MathNet.Numerics.Distributions.ContinuousUniform()


/// these are the different methods we can use to compute our predictors
type basisType =
    | cone = 0 // convex cone, assumes only positive predictors
    | gauss = 1 // standard least squares
    | tls = 2 //  total least squares, allows error in the model
    | NNMF = 3 // non negative matrix factorisation
    | NNLS = 4 // Least Squares, constrain x>0

let basisTypeToString (basisT:basisType) =
    match basisT with
        | basisType.cone -> "convex_cone"
        | basisType.gauss -> "vector_space"
        | basisType.tls -> "total_least_square"
        | basisType.NNMF -> "non_negative_matrix_factorisation"
        | basisType.NNLS -> "non_negative_least_squares"
        | _ -> "unknown"


/// extracts modelSize and testSize rows from M randomly and returns the model and test matrices
let extractModel (M:DenseMatrix) modelSize testSize =
    let r = new System.Random()
    let indices = Seq.init (M.RowCount) (fun i -> i,r.NextDouble()) |> Seq.sortBy (fun (i,v) -> v) |> Seq.map fst |> Seq.take (modelSize + testSize)
    let indicesModel = indices |> Seq.take modelSize
    let indicesTest = indices |> Seq.skip modelSize
    let matrixModel = DenseMatrix.OfRowVectors(indicesModel |> Seq.map (fun i -> M.Row(i)) |> Seq.toArray)
    let matrixTest = DenseMatrix.OfRowVectors(indicesTest |> Seq.map (fun i -> M.Row(i)) |> Seq.toArray)
    matrixModel, matrixTest

/// find the best basis out of the M matrix, and returns:
/// the indices of the basis
/// the names of the programs in the basis
/// the estimated basis quality (0 means good)
let findBasis (basisT:basisType) (M:DenseMatrix) basisSize =
    let data, eval, evect, info = Solvers.PCA (DenseMatrix.OfMatrix(M.Transpose())) 4
    //System.Console.WriteLine("data: {0}", data.ToString(100,100))
    //System.Console.WriteLine("info: {0}", info)
    
    //let data, eval, evect, info = PCA (DenseMatrix.OfMatrix(M.Transpose())) 4
    let basisIndices, centroids, cost = Solvers.kmean (DenseMatrix.OfMatrix(data)) basisSize
    
    //let dataToPlot = Array.init (data.RowCount) (fun i -> data.Row(i)) |> Array.map (fun p -> p.[0],p.[1])
    //let centroidsToPlot = centroids |> Array.map (fun c -> c.[0],c.[1])
    //[| dataToPlot |> FSharpChart.Point :> ChartTypes.GenericChart ; centroidsToPlot |> FSharpChart.Point :> ChartTypes.GenericChart |] |> FSharpChart.Combine |> FSharpChart.Create |> ignore
    let basisNames = [| " " |]
    basisIndices, basisNames, cost, info

let estimatedComputationalPatterns = ref 2

/// find the predictor given the type, a predictor is function that takes a matrix and gives back a prediction and an expected error
let findPredictors (basisT:basisType) (A:DenseMatrix) (b:DenseVector) =
    let getRow (measures:float[][]) i =
        measures |> Array.map (fun r -> r.[i])
    let filterRows (measures:float[][]) (indices:int[]) =
        let filterRow (r:float[]) =
            r |> Array.mapi (fun i v -> i,v) |> Array.filter (fun (i,v) -> indices |> Array.exists ((=) i) ) |> Array.map snd
        measures |> Array.map filterRow

    // performs a prediction and returns it with the confidence
    let predict (aTest:DenseVector) =
        match basisT with
        | basisType.NNLS ->
            Solvers.predictUsingNonNegativeLeastSquares A b aTest
        | basisType.NNMF ->
            Solvers.predictUsingNonNegativeMatrixFactorization A b aTest (!estimatedComputationalPatterns)
        | basisType.cone ->
            // TODO
            0.0, 0.0
        | basisType.gauss ->
            Solvers.predictUsingOrdinaryLeastSquares A b aTest
        | basisType.tls ->
            Solvers.predictUsingTotalLeastSquares A b aTest
    predict

/// execute one full experiment
/// returns the average error, errors standard deviations, RMSE and the list of all the errors (to compute the overall rmse)
let runOneExperiment (M:DenseMatrix) (basisT:basisType) modelSize testSize basisSize targetProgram =
    // extract random rows for the model and test matrices
    let matrixModelAllPrograms, matrixTestAllPrograms = extractModel M modelSize testSize
    //System.Console.WriteLine("matrixModelAllPrograms {0}", matrixModelAllPrograms.ToString())
    //System.Console.WriteLine("matrixTestAllPrograms {0}", matrixTestAllPrograms.ToString())
    // find the basis (the surrogates)
    let matrixModelNoTarget = DenseMatrix.OfColumnVectors( Seq.init (matrixModelAllPrograms.ColumnCount) (id) |> Seq.filter (fun i -> not (i = targetProgram)) |> Seq.map (fun i -> matrixModelAllPrograms.Column(i)) |> Seq.toArray)
    let matrixTestNoTarget = DenseMatrix.OfColumnVectors( Seq.init (matrixTestAllPrograms.ColumnCount) (id) |> Seq.filter (fun i -> not (i = targetProgram)) |> Seq.map (fun i -> matrixTestAllPrograms.Column(i)) |> Seq.toArray)
    let basisIndices, basisNames, distance, info = findBasis basisT matrixModelNoTarget basisSize
    //System.Console.WriteLine("targetProgram {0}", targetProgram)
    //System.Console.WriteLine("basisIndices: ")
    //basisIndices |> Array.iter (fun i -> System.Console.Write(" {0}", i))
    //System.Console.WriteLine("")
    
    // get the matrix of measures of surrogates for the model and for the test
    let testbedModel = DenseMatrix.OfColumnVectors( Seq.init (matrixModelNoTarget.ColumnCount) (id) |> Seq.filter (fun i -> basisIndices |> Seq.filter (fun j -> j = i) |> Seq.length > 0 ) |> Seq.map (fun i -> matrixModelNoTarget.Column(i)) |> Seq.toArray)
    let testbedTest = DenseMatrix.OfColumnVectors( Seq.init (matrixTestNoTarget.ColumnCount) (id) |> Seq.filter (fun i -> basisIndices |> Seq.filter (fun j -> j = i) |> Seq.length > 0 ) |> Seq.map (fun i -> matrixTestNoTarget.Column(i)) |> Seq.toArray)
    // get the measures of the target program for model and test
    let measuresTargetModel = matrixModelAllPrograms.Column(targetProgram)
    let measuresTargetTest = matrixTestAllPrograms.Column(targetProgram)
    //System.Console.WriteLine("testbedModel: {0}", testbedModel.ToString())
    //System.Console.WriteLine("measuresTargetModel: {0}", measuresTargetModel.ToString())
    //System.Console.WriteLine("testbedTest: {0}", testbedTest.ToString())
    //System.Console.WriteLine("measuresTargetTest: {0}", measuresTargetTest.ToString())
    // find the performance prediction function
    let predictor = findPredictors basisT testbedModel (DenseVector.OfEnumerable(measuresTargetModel))
    let predictOne (a:DenseVector) (measured:float) =
        let prediction, confidence = predictor a
        let error = (prediction - measured)/measured
        //System.Console.WriteLine("a:{0}", a.ToString())
        //System.Console.WriteLine("error {0} confidence {1} predicted {2} measured {3}", error, confidence, prediction, measured)
        error, confidence
    let predictions = Seq.init (testbedTest.RowCount) (id) |> Seq.map (fun i -> predictOne (DenseVector.OfVector(testbedTest.Row(i))) (measuresTargetTest.Item(i)) ) 
    let errors = predictions |> Seq.map fst
    let confidence = predictions |> Seq.map snd
    let errorsConfidenceCorrelation = MathNet.Numerics.Statistics.Correlation.Pearson(errors, confidence)
    //System.Console.WriteLine("errorsConfidenceCorrelation={0}", errorsConfidenceCorrelation)
    // TODO: do something with predictions!
    let average = errors.Mean()
    let stdDev = errors.StandardDeviation()
    let rmse = errors |> Seq.map (fun v -> v*v) |> Seq.average |> sqrt
    average, stdDev, rmse, errors


// runOneExperiment (basisType.gauss) 100 30 15 29
// run the experiment several times and calculate statistics
/// executes a bunch of experiments with the given setup
/// returns averages.Mean(), averages.StandardDeviation(), stdDev.Mean(), stdDev.StandardDeviation(), rmse.Mean(), rmse.StandardDeviation(), errors.Mean(), errors.StandardDeviation(), errorsRmse, errors
let runSeveralExperiments (M:DenseMatrix) (basisT:basisType) modelSize testSize basisSize iter targetProgram =
    let predictions = Seq.init iter (fun  _ -> runOneExperiment M basisT modelSize testSize basisSize targetProgram) |> Seq.cache
    let averages = predictions |> Seq.map (fun (average, stdDev, rmse, errors) -> average)
    let stdDev = predictions |> Seq.map (fun (average, stdDev, rmse, errors) -> stdDev)
    let rmse = predictions |> Seq.map (fun (average, stdDev, rmse, errors) -> rmse)
    let errors = predictions |> Seq.map (fun (average, stdDev, rmse, errors) -> errors) |> Seq.concat
    let errorsRmse = errors |> Seq.map (fun v -> v*v) |> Seq.average |> sqrt
    //averages.Mean(), averages.StandardDeviation(), stdDev.Mean(), stdDev.StandardDeviation(), rmse.Mean(), rmse.StandardDeviation(), errors.Mean(), errors.StandardDeviation(), errorsRmse, errors
    errorsRmse, errors



// take measures from the other script (SPECCPU.fsx)
let values_array = measures
let names_array = names

/// performs a seq of experiments with the given parameters on all the possible targets
let runExperimentsAllPrograms  (M:DenseMatrix)  (basisT:basisType) modelSize testSize basisSize iter =
    let predictions = Seq.init (values_array.[0].Length) (fun i -> i, runSeveralExperiments M basisT modelSize testSize basisSize iter i)
    predictions

let printAllExperiments (predictions:int*(float*seq<float>)) (modelSize:int) (testSize:int) (basisSize:int) target = 
    let mapIndex i t = if i < target then i else i+1
    let printProgram (p:int*(float*seq<float>)) =
        let idx,(rmse,errs) = p
        let name = names_array.[mapIndex idx]
        let filename = System.String.Format(@"{0}{1}_modelSize{2}_testSize{3}_{4}.dat", folder, name, modelSize,testSize,basisSize)
        System.IO.File.WriteAllText(folder + "correlation.txt", sb.ToString())    
    ()

open System.Threading

// transform measures into a Dense Matrix
let valuesSequence = Seq.init (values_array.Length) (fun i -> values_array.[i] |> Array.toSeq)
let M = DenseMatrix.OfMatrix(DenseMatrix.OfRows(values_array.Length, values_array.[0].Length, valuesSequence).NormalizeRows(1))


let e,ers = runSeveralExperiments M (basisType.gauss) 500 1 25 10 0
ers |> Seq.length

let predictions = runExperimentsAllPrograms M (basisType.gauss) 50 30 20 10 |> Seq.toArray
let prog_err = predictions |> Array.map (fun (i,(_,_,_,_,_,_,_,_,v,_)) -> i,v )


let valuesSequence = Seq.init (values_array.Length) (fun i -> values_array.[i] |> Array.toSeq)
let M = DenseMatrix.OfRows(values_array.Length, values_array.[0].Length, valuesSequence).NormalizeRows(2).Transpose()
let basisIndices, basisNames, distance, info = findBasis basisType.gauss (DenseMatrix.OfMatrix(M)) 4

let proj, _, _, info = PCA (DenseMatrix.OfMatrix(M)) 29
let proj_points = Array.init 29 (fun i -> i, proj.Row(i).AsEnumerable() |> Seq.toArray)



// correlatione tra errori e coordinate dei punti nei components
let correlations = Array.init 29 (fun i -> i, MathNet.Numerics.Statistics.Correlation.Pearson(prog_err |> Array.map snd, proj_points |> Array.map (fun (j,v) -> v.[i])))
correlations |> Array.sortBy (fun (i,v) -> v*v) |> Array.rev

let predictErr prog =
    let i, p = proj_points.[prog]
    let estimatedErr = max(0.0) (Array.map2 (fun coord (i,err) -> coord*err) p correlations |> Array.sum)
    let realerr = prog_err.[prog] |> snd
    estimatedErr/realerr, estimatedErr, realerr
Array.init 29 (fun i -> predictErr i)


let A = DenseMatrix.OfRowsCovariant(3,2, [| [| 1.0; 0.0 |]; [| 1.0; 2.0 |]; [| 0.0; 1.0 |]; |])
let A = M
let principalComponents = 4
//let PCA2 (A:DenseMatrix) principalComponents =
// subtract the mean of each column to each column
let A1 = DenseMatrix.OfColumnVectors(Array.init (A.ColumnCount) (fun i -> 
                                    let c = A.Column(i) 
                                    c.Subtract(c.Mean())
                                ))
// covariance matrix
let covMatrix = DenseMatrix.Create(A1.ColumnCount, A1.ColumnCount, fun i j -> MathNet.Numerics.Statistics.ArrayStatistics.Covariance(A1.Column(i).AsEnumerable() |> Seq.toArray, A1.Column(j).AsEnumerable() |> Seq.toArray))
// eigen values and vector of the covariance matrix
let fact = covMatrix.Evd()
let eigenValues = fact.EigenValues()
let eigenVectors = fact.EigenVectors()
let orderedEigenValues = eigenValues.AsEnumerable() |> Seq.mapi (fun i v -> i, v.Magnitude) |> Seq.sortBy snd |> Seq.skip (eigenValues.Count - principalComponents)
let totenergy = eigenValues.AsEnumerable() |> Seq.map (fun v -> v.Magnitude) |> Seq.sum
let energy = orderedEigenValues |> Seq.map snd |> Seq.sum
let rowFeatureVector = DenseMatrix.OfRowVectors( orderedEigenValues |> Seq.map fst |> Seq.map (fun i -> eigenVectors.Column(i)) |> Seq.toArray |> Array.rev)
let A1T = A1.Transpose()
let finalData = rowFeatureVector.Multiply(A1T).Transpose()
//let dataToReconstruct = finalData.Append(DenseMatrix.zeroCreate (A1.RowCount) (A1.ColumnCount - finalData.ColumnCount))
let reconstructed = rowFeatureVector.Transpose().Multiply(finalData.Transpose()).Transpose()
let diff = reconstructed.Subtract(A1)
let mag = A1.Transpose().Multiply(A1)
let magDiff = diff.Transpose().Multiply(diff)
let info = energy/totenergy
let orderedMagDiff = Array.init 29 (fun i -> i,( magDiff.Item (i,i)) / ( mag.Item (i,i)) ) |> Array.sortBy snd |> Array.rev
finalData, eigenValues, eigenVectors, energy/totenergy

covMatrix.Column(0).AsEnumerable() |> Seq.iter (fun v -> System.Console.Write(" {0}" ,v))





// ------------------- test approach with toy data using non linear behaviour (amdahl) ------------------- 

let amdahl time serial threads = time*(serial+(1.0-serial)/float(threads))
let r = new System.Random()
let createMachine () =
    let tm = r.NextDouble()+0.01
    let n = int(float(2) ** float(r.Next(8)))
    tm, n
let createProgram () =
    let tp = r.NextDouble() + 0.01
    let serial = r.NextDouble()
    tp, serial

let machines = Array.init 10 (fun _ -> createMachine ())
let programs = Array.init 10 (fun _ -> createProgram ())

let rows = machines |> Array.map (fun (tm,threads) -> programs |> Seq.map (fun (tp,serial) ->  System.Console.WriteLine("amdahl {0}*{1} {2} {3}", tp, tm, serial, threads); amdahl (tp*tm) serial threads ) )
//let N = DenseMatrix.OfMatrix(DenseMatrix.OfRows(machines.Length, programs.Length, rows).NormalizeRows(2))
let N = DenseMatrix.OfRows(machines.Length, programs.Length, rows)

runSeveralExperiments N (basisType.NNMF) 2 1 2 10 1

runOneExperiment N (basisType.NNLS) 4 1 2 0

let proj, eigenva, eigenve, info = PCA (DenseMatrix.OfMatrix(N.Transpose())) 2
let proj, eigenva, eigenve, info = PCA N 2

Array.init (proj.RowCount) (fun i -> proj.Row(i).[0], proj.Row(i).[1]) |> FSharpChart.Point |> FSharpChart.Create
Array.init (N.RowCount) (fun i -> N.Row(i).[0], N.Row(i).[1]) |> FSharpChart.Point |> FSharpChart.Create

rows.[2] |> Seq.head
let H,W,c = NMF N 2
//N.Subtract(W.Multiply(H))

let N = DenseMatrix.OfRowsCovariant(3, 3, [| [| 1.0; 1.0; 1.0 |]; [| 2.0; 3.0; 4.0 |]; [|3.0; 4.0; 5.0 |] |])
let Na = N.SubMatrix(0,2,0,2)
let H,W,c = NMF (DenseMatrix.OfMatrix(Na)) 1
let a = DenseVector.ofSeq( N.Row(2).AsEnumerable() |> Seq.take 2)
let b = DenseVector.ofSeq(N.Column(2).AsEnumerable() |> Seq.take 2)


let predictNMF (H:DenseMatrix) (W:DenseMatrix) (b:DenseVector) (a:DenseVector) =
    //let w = H.Transpose().Svd(true).Solve(a)
    let w = NNLS (DenseMatrix.OfMatrix(H.Transpose())) a
    //let h = W.Svd(true).Solve(b)
    let h = NNLS W b
    let prev = h.ToRowMatrix().Multiply(w)
    prev.Item(0)
let H,W,c = NMF (DenseMatrix.OfMatrix(Na)) 2
let predicted = predictNMF H W b a
predicted, c
N.Item(2,2)

let A = DenseMatrix.OfMatrix(N.SubMatrix(0,3,0,2))
let b = DenseVector.ofSeq(N.Column(2).AsEnumerable() |> Seq.take 3)
let x = Solvers.NNLS A b

open MathNet.Numerics.LinearAlgebra.Double
open MathNet.Numerics

#r @"C:\Users\davidemorelli\Documents\GitHub\Energon\Solvers\bin\Debug\Solvers.dll"
open Solvers

open System.Collections.Generic


// --------------------- TEST SOLVERS --------------------


let NNLS (A:DenseMatrix) (b:DenseVector) =
    let r = new System.Random()
    // see http://books.google.it/books?hl=en&lr=&id=LU5_2sWlVlMC&oi=fnd&pg=PP2&ots=x2kEt5s5kG&sig=HbeDhVWlooj91jYrD8pR9k5mzLk&redir_esc=y#v=onepage&q&f=false
    // pag 161
    let n = A.ColumnCount
    // step 1
    let P = []
    let Z = [0..(n-1)]

    let steps2to5 (x:DenseVector) (z:DenseVector) (P:int list) (Z:int list) f =
        // step 2
        let w = A.Transpose().Multiply(b - A.Multiply(x))
        // step 3
        if (Z.IsEmpty || Z |> List.map (fun j -> w.Item(j) <= 0.0) |> List.forall (id)) then
            x
        else
            // step 4
            let t,max = Z |> List.map (fun j -> j, w.Item(j)) |> List.maxBy (fun (j,v) -> v)
            // step 5
            let P2 = t::P
            let Z2 = Z |> List.filter (fun j -> j <> t)
            f x z P2 Z2

    let rec steps6to11 (x:DenseVector) (z:DenseVector) (P:int list) (Z:int list) =
        // step 6
        let Ap = DenseMatrix.ofColumnVectors( P |> List.map (fun j -> A.Column(j)) )
        let zp = Ap.QR().Solve(b)
        let z = DenseVector.zeroCreate(n)
        P |> List.iteri (fun i v -> z.Item(v) <- zp.Item(i) )
        // step 7
        if (P |> List.map (fun j -> z.Item(j) > 0.0) |> List.forall (id)) then
            //printf "go to step 2\n"
            // iterate
            steps2to5 z z P Z steps6to11
        else
            // continue
            // step 8
            let q,min = P |> List.filter (fun j -> z.Item(j)<=0.0 ) |> List.map (fun j -> j, x.Item(j)/(x.Item(j) - z.Item(j))) |> List.minBy (snd)
            // step 9
            let alpha = x.Item(q)/(x.Item(q) - z.Item(q))
            // step 10
            let x = x + (z.Subtract(x).Multiply(alpha))
            // step 11
            let commuters = P |> List.filter (fun j -> x.Item(j) = 0.0)
            let Z2 = List.append Z commuters
            let P2 = P |> List.filter (fun j -> not(commuters.Contains(j)))
            // go to step 6
            steps6to11 (DenseVector.OfVector(x)) (DenseVector.OfVector(z)) P2 Z2

    steps2to5 (DenseVector.zeroCreate(n)) (DenseVector.zeroCreate(n)) P Z steps6to11


let NNLS2 (A:float[][]) (b:float[]) =
    let A2 = DenseMatrix.OfRowsCovariant(A.Count(), A.[0].Count(), A)
    let b2 = DenseVector.ofList (b |> Array.toList)
    let x = NNLS A2 b2
    x.AsEnumerable() |> Seq.toArray

let TotalLeastSquare (X:float[][]) (y:float[]) =
    let m = y |> Array.length
    let n = X.[0] |> Array.length
    let Xmat = DenseMatrix.OfRowsCovariant(X.Length, X.[0].Length, X)
    let Ymat = DenseMatrix.OfRowsCovariant(y.Length, 1, y |> Array.map (fun v -> [| v |]))
    let Zmat = Xmat.Append(Ymat)
    let svd = Zmat.Svd(true)
    let Smat = svd.S()
    let Umat = svd.U()
    let VTmat = svd.VT()
    let Vmat = VTmat.Transpose()
    let VXY = Vmat.SubMatrix(0, n, n, (Vmat.ColumnCount - n))
    let VYY = Vmat.SubMatrix(n, (Vmat.RowCount - n), n, (Vmat.ColumnCount - n))
    let B = (-VXY).Divide(VYY.At(0,0))
    B.Column(0).ToArray()

let Gauss (testbed_model:float[][]) (model:float[]) =
    //let testbedAsIenum = testbed_model |> Array.map (fun row -> new MathNet.Numerics.LinearAlgebra.Double.DenseVector(row) :>  MathNet.Numerics.LinearAlgebra.Double.Vector)
    let X = DenseMatrix.OfRowsCovariant(testbed_model.Length, testbed_model.[0].Length, testbed_model)
    X.Svd(true).Solve(new DenseVector(model)) |> Seq.toArray

let simplex (testbed_model:float[][]) (model:float[]) =
    let getRow (measures:float[][]) i =
        measures |> Array.map (fun r -> r.[i])
    let filterRows (measures:float[][]) (indices:int[]) =
        let filterRow (r:float[]) =
            r |> Array.mapi (fun i v -> i,v) |> Array.filter (fun (i,v) -> indices.Contains(i)) |> Array.map snd
        measures |> Array.map filterRow
    let s = new SplitupFinder()
    let programs = Array.init (testbed_model.[0].Length) (id) |> Array.map (getRow testbed_model) |> Array.map (fun r -> 
            let p = new Program()
            p.Measures <- r
            p
        )
    s.Testbed <- programs
    let p = new Program()
    p.Measures <- model
    s.Target <- p
    let splitup = 
        if (s.FindSplitup(true)) then
            s.Splitup
        else
            [| |]
    splitup

let runBatch solver errX erry multiplier =
    let rows = 10
    let cols = 10
    let err sol solreal X = 
        let Xrand = X |> Array.map (fun (row:float[]) -> row |> Array.map (fun (v:float) -> v + v*(r.NextDouble()*errX*2.0 - errX)))
        let y = X |> Array.map (fun (row:float[]) -> Array.map2 (*) row solreal |> Array.sum) |> Array.map (fun v -> v + v*(r.NextDouble()*erry*2.0 - erry))
        let sum = Array.zip Xrand y |> Array.map (fun (x,y) -> 
            let predicted = Array.zip x sol |> Array.sumBy (fun (x,s) -> x*s)  
            (predicted - y)/y ) |> Array.map (fun e -> e*e) |> Array.sum
        let avg = sum / float(y |> Array.length)
        sqrt(avg)

    let runOne() =
        let X = Array.init (rows*10) (id) |> Array.map (fun _ -> Array.init (cols) (fun _ -> r.NextDouble() *multiplier)  )
        let Xrand, y, solreal = 
            let Xrand = X |> Array.map (fun (row:float[]) -> row |> Array.map (fun (v:float) -> v + v*(r.NextDouble()*errX*2.0 - errX)))
            let solreal = Array.init (X.[0] |> Array.length) (id) |> Array.map (fun _ -> r.NextDouble())
            let y = X |> Array.map (fun (row:float[]) -> Array.map2 (*) row solreal |> Array.sum) |> Array.map (fun v -> v + v*(r.NextDouble()*erry*2.0 - erry))
            Xrand, y, solreal
        let sol = solver Xrand y
        GC.WaitForFullGCComplete()
        let solErr = sqrt((Array.map2 (fun v1 v2 -> (v1-v2)) sol solreal |> Array.map (fun v -> v*v) |> Array.sum)/float(sol.Length))
        (err sol solreal X, solErr), (sol, solreal)
    let errs, sols = Array.init 100 (id) |> Array.map (fun _ -> runOne()) |> Array.unzip
    let err, solerr = errs |> Array.unzip
    let sol, solreal = sols |> Array.unzip
    err |> Array.average, solerr |> Array.average//, sol, solreal

let err = 1.0
let testerr err=
    let errNNLS = runBatch NNLS2 err err 1.0
    let errGauss = runBatch Gauss err err 1.0
    let errTLS = runBatch TotalLeastSquare err err 1.0
    let errSimplex = runBatch simplex err err 1.0
    GC.WaitForFullGCComplete()
    err, errGauss, errTLS, errSimplex, errNNLS

let errors = Array.init 100 (fun i -> float(i)*0.01) |> Array.map testerr

errors |> Array.iter (fun (e, (g1,g2),(t1,t2),(s1,s2),(nnls_avg,nnls_stddev)) -> System.Console.WriteLine(System.String.Format("{0} {1} {2} {3} {4} {5} {6} {7} {8}", e, g1,t1,s1,nnls_avg, g2,t2,s2,nnls_stddev )))


testerr 0.1


// test the computational pattern idea...

let generateVector n = Array.init n (id) |> Array.map (fun _ -> r.NextDouble() )
let generateMatrix rows cols = Array.init (rows) (id) |> Array.map (fun _ -> generateVector cols)
let generateMatrixFromMatrix (A:float[][]) = DenseMatrix.OfRowsCovariant(A.Length, A.[0].Length, A) 


// TEST
let n_machines_model = 10
let n_machines_test = 100
let n_computational_patterns = 30
let n_predictors = 10
let testPredictors solver n_machines_model n_machines_test n_computational_patterns n_predictors =
    let testSingle () =
        let A_alpha = generateMatrix n_machines_model n_computational_patterns
        let X_alpha = generateMatrix n_computational_patterns (n_predictors + 1)
        let A_alpha_m = generateMatrixFromMatrix A_alpha
        let X_alpha_m = generateMatrixFromMatrix X_alpha
        let A_m = A_alpha_m.Multiply X_alpha_m

        let b_model = A_m.Column(0) |> Seq.toArray
        let A_model = Array.init (A_m.RowCount) (id) |> Array.map (fun i -> A_m.Row(i) |> Seq.skip 1 |> Seq.toArray)

        let x = solver A_model b_model

        let A_alpha_test = generateMatrixFromMatrix (generateMatrix n_machines_test n_computational_patterns)
        let A_test_m = A_alpha_test.Multiply X_alpha_m
        let b_test = A_test_m.Column(0) |> Seq.toArray
        let A_test = Array.init (A_test_m.RowCount) (id) |> Array.map (fun i -> A_test_m.Row(i) |> Seq.skip 1 |> Seq.toArray)

        let err = 
            let A = generateMatrixFromMatrix A_test
            let b = DenseVector.OfEnumerable(b_test)
            let x_v = DenseVector.OfEnumerable(x)
            let pred = A.Multiply x_v
            let err = pred - b
            let sum = err.ToArray() |> Array.map2 (fun v diff -> diff/v) (b.ToArray()) |> Array.map (fun v -> v*v) |> Array.sum
            sqrt(sum/float(err.Count))
        err
    let errors = Array.init 100 (id) |> Array.map (fun _ -> testSingle())
    let avg = errors |> Array.average
    let rmse = sqrt((errors |> Array.map (fun v -> v-avg) |> Array.map (fun v -> v*v) |> Array.sum)/float(errors.Length))
    avg, rmse

testPredictors Gauss 100 100 33 28
testPredictors TotalLeastSquare 100 1 33 28
testPredictors simplex 100 100 33 28








    
#I @"C:\Users\davidemorelli\AppData\Roaming\Local Libraries\Local Documents\GitHub\Energon\Charts"
#r "MSDN.FSharpChart.dll"
open MSDN.FSharp.Charting



// test
let modelSize = 2
let realNumberOfCompPatterns = 3
let numberOfSurrogates = 2
let pc = 2

let runOne realNumberOfCompPatterns estimatedCompPatterns numberOfSurrogates modelSize  =
    let r = new ContinuousUniform(0.0, 1.0)
    let realW = DenseMatrix.CreateRandom(modelSize+1, realNumberOfCompPatterns, r)
    let realH = DenseMatrix.CreateRandom(realNumberOfCompPatterns, numberOfSurrogates+1, r)
    let A = realW.Multiply(realH)
    let AforModel = A.SubMatrix(0,A.RowCount - 1, 0, A.ColumnCount - 1)
    let b = A.Column(A.ColumnCount - 1).SubVector(0, A.RowCount - 1)
    let newResource = A.Row(A.RowCount - 1)
    let knownMeasuresNewResource = newResource.SubVector(0, newResource.Count - 1)
    let target = newResource.ElementAt(newResource.Count - 1)
    let prediction = predictNMF estimatedCompPatterns (DenseMatrix.OfMatrix(AforModel)) (DenseVector.OfVector(b)) (DenseVector.OfVector(knownMeasuresNewResource))
    //let prediction = Seq.init 30 (id) |> Seq.map (fun _ -> predictNMF estimatedCompPatterns (DenseMatrix.OfMatrix(AforModel)) (DenseVector.OfVector(b)) (DenseVector.OfVector(knownMeasuresNewResource))) |> Seq.sort |> Seq.head
    let error = (prediction - target) / target
    error

let runSeveral real estimated surr modsize = Seq.init 1000 (fun _ -> runOne real estimated surr modsize) |> Seq.toArray  |> Array.map (fun v -> v*v) |> Array.average |> sqrt 

//runSeveral 3 3 5 5
//runOne 3 3 5 5

let realCompPatternsArray = Array.init 5 (fun i -> i+1)
let estimatedCompPatternsArray = Array.init 5 (fun i -> i+1)
let surrogatesArray = Array.init 5 (fun i -> i+1)
let modelsizeArray = Array.init 5 (fun i -> i+1)

let sb = new System.Text.StringBuilder()

let stopNMF = ref false
let testNMFAsynch () =
    new Thread(fun () -> 
            realCompPatternsArray |>  Array.iter (fun real ->
                            estimatedCompPatternsArray  |>  Array.iter (fun estimated ->
                                surrogatesArray |> Array.iter (fun surr ->
                                    modelsizeArray |> Array.iter (fun modsize ->
                                        if !stopNMF then
                                            raise (Exception("NMF stopped"))
                                        let res = runSeveral real estimated surr modsize
                                        sb.AppendFormat("{0} {1} {2} {3} {4}\n", real, estimated, surr, modsize, res) |> ignore
                                        System.Console.WriteLine("NMF: {0} {1} {2} {3} {4}\n", real, estimated, surr, modsize, res)
                                        )
                                    )
                                )
                            )
                        )
        
let t3 = testNMFAsynch()
t3.Start()

stopNMF := false

sb.ToString()
System.IO.File.WriteAllText("C:\\Data\\NMF.dat", sb.ToString())



let resArray = realCompPatternsArray |>  Array.map (fun real ->
                estimatedCompPatternsArray  |>  Array.map (fun estimated ->
                    surrogatesArray |> Array.map (fun surr ->
                        modelsizeArray |> Array.map (fun modsize ->
                            let res = runSeveral real estimated surr modsize
                            System.Console.WriteLine("NMF: {0} {1} {2} {3} {4}\n", real, estimated, surr, modsize, res)
                            res
                            )
                        )
                    )
                )
let resArrayOld = resArray

realCompPatternsArray |>  Array.iter (fun real ->
                estimatedCompPatternsArray  |>  Array.iter (fun estimated ->
                    surrogatesArray |> Array.iter (fun surr ->
                        modelsizeArray |> Array.iter (fun modsize ->
                            let res = resArray.[real-1].[estimated-1].[surr-1].[modsize-1]
                            if (res > 1.0) then
                                System.Console.WriteLine("NMF: real={0} estimated={1} surr={2} modsize={3} error={4}", real, estimated, surr, modsize, res)
                            )
                        )
                    )
                )


let test1 = realCompPatternsArray |>  Array.map (fun real ->
                estimatedCompPatternsArray  |>  Array.map (fun estimated ->
                    surrogatesArray |> Array.map (fun surr ->
                        modelsizeArray |> Array.map (fun modsize ->
                            float(estimated), resArray.[real-1].[estimated-1].[surr-1].[modsize-1]
                            )
                        )
                    )
                ) |> Array.concat |> Array.concat |> Array.concat |> Array.filter (fun (i,v) -> v<1.0)

test1 |> FSharpChart.Point |> FSharpChart.Create

MathNet.Numerics.Statistics.Correlation.Pearson(test1 |> Array.map (fun (i,v) -> float(i),v) |> Array.unzip)













// -------------- GET DATA FROM www.spec.org ----------------
// the following code retrieves the results from the SEC web site and stores the data in a sqllite db

Console.WriteLine("downloading index...")
let cpuspeckind = "INT"
let baseaddr = "http://www.spec.org/cpu2006/results/cint2006.html" 
//let cpuspeckind = "FP"
//let baseaddr = "http://www.spec.org/cpu2006/results/cfp2006.html" 
let wc = new System.Net.WebClient()
let content = wc.DownloadString(baseaddr)
Console.WriteLine("...index downloaded")

open System.Text.RegularExpressions

let urls = seq {
  let urlsL = Regex.Matches(content, @"href=""(.*\.csv)""")
  for i in 0..(urlsL.Count-1) do
    yield urlsL.Item(i).Groups.Item(1).Value
  }

//let firstCsv = urls |> Seq.head

let processUrl firstCsv =
    let addr = "http://www.spec.org/cpu2006/results/" + firstCsv
    printfn "fetching %s" addr
    System.Threading.Thread.Sleep(500)
    let wc = new System.Net.WebClient()
    let content = wc.DownloadString(addr)
    if content.StartsWith("valid,1") then
        let righe = content.Split([| '\n' |])
        let stuff = Regex.Matches(content, @"Selected.Results.Table([\s\S]*)HARDWARE([\s\S]*)SOFTWARE([\s\S]*)Base.Compiler.Invocation")
        let results = stuff.Item(0).Groups.Item(1).Value
        let hw = stuff.Item(0).Groups.Item(2).Value
        let sw = stuff.Item(0).Groups.Item(3).Value
        let resultsLines = results.Split([|'\n'|])
        let foldProg (progs: (string*double*double*double*double) list) (line:string) =
            let tags = line.Split([|','|])
            let progName = tags.[0]
            if (Regex.Match(line, @"^\d\d\d[\S\s]*").Captures.Count > 0) then
                let tagT1 = tags.[1]
                let tagT2 = tags.[2]
                let tagT3 = tags.[6]
                let tagT4 = tags.[7]
                let b1, d1 = Double.TryParse(tagT1)
                let b2, d2 = Double.TryParse(tagT2)
                let b3, d3 = Double.TryParse(tagT3)
                let b4, d4 = Double.TryParse(tagT4)
                if (b1 && b2 && b3 && b4) then
                    System.Console.WriteLine(@"{0} {1} {2} {3} {4} ", tags.[0], tagT1, tagT2, tagT3, tagT4)
                    (progName,double(tagT1),double(tagT2),double(tagT3),double(tagT4))::progs
                else
                    System.Console.WriteLine(@"could noty parse {0} {1}", tags.[0], line)
                    progs
            else
                progs
        let progs = resultsLines |>  Seq.fold foldProg (List.empty<string*double*double*double*double>)
        let getItem (l:string) (item:string) =
            let filterForItem (line:string) =        
                let tags = line.Split([|','|])
                let name = tags.[0].Replace("\"","")
                if (name.Equals(item)) then
                    true
                else
                    false
            let res = l.Split([|'\n'|]) |> Seq.find filterForItem
            res.Substring(res.IndexOf(",")+1).Replace("\"","")
        let createExp (n:string,v1:double,v2:double, v3:double, v4:double) = helper.SaveNewExperiment(dbfile, firstCsv, getItem hw "CPU Name", getItem hw "CPU MHz", getItem hw "FPU", getItem hw "Memory", getItem sw "Operating System", getItem sw "Compiler", n, new decimal(v1), new decimal(v2), new decimal(v3), new decimal(v4), cpuspeckind);
        let res = progs |> Seq.iter createExp
        GC.WaitForFullGCComplete()
        res

let specRawDataSubfolder = @"SPEC_CPU_RAW_DATA\"
let saveUrl (firstCsv:string) =
    let targetFile = folder + specRawDataSubfolder + cpuspeckind + "_" + firstCsv.Substring(firstCsv.IndexOf("/") + 1 )
    if (System.IO.File.Exists(targetFile)) then
        System.Console.WriteLine(targetFile + " exists, skipping")
    else
        let addr = "http://www.spec.org/cpu2006/results/" + firstCsv
        printfn "fetching %s" addr
        System.Threading.Thread.Sleep(500)
        let wc = new System.Net.WebClient()
        let content = wc.DownloadString(addr)
        if content.StartsWith("valid,1") then
            System.IO.File.WriteAllText(targetFile , content)
            GC.WaitForFullGCComplete() |> ignore

// save directly in DB
// only process the first 2
//urls |> Seq.take 2 |> Seq.iter processUrl

// do all of them
//urls |> Seq.iter processUrl

// don't process anything before a certain url (useful in case network connection is lost, to resume the job) 
//urls |> Seq.fold (fun s u -> if s then processUrl u; true else if u.Equals(@"res2010q2/cpu2006-20100510-10888.csv") then true else false) false  



// save as files to folder

// only process the first 2
//urls |> Seq.take 2 |> Seq.iter saveUrl

// do all of them
urls |> Seq.iter saveUrl

// don't process anything before a certain url (useful in case network connection is lost, to resume the job) 
//urls |> Seq.fold (fun s u -> if s then processUrl u; true else if u.Equals(@"res2010q2/cpu2006-20100510-10888.csv") then true else false) false  

urls |> Seq.length
urls |> Seq.skip 4000



let processFile firstCsv =
    let targetFile = folder + specRawDataSubfolder + firstCsv
    let cpuspeckind = if (firstCsv.StartsWith("FP")) then "FP" else "INT"
    let content = System.IO.File.ReadAllText(targetFile)
    if content.StartsWith("valid,1") then
        let righe = content.Split([| '\n' |])
        let stuff = Regex.Matches(content, @"Selected.Results.Table([\s\S]*)HARDWARE([\s\S]*)SOFTWARE([\s\S]*)Base.Compiler.Invocation")
        let results = stuff.Item(0).Groups.Item(1).Value
        let hw = stuff.Item(0).Groups.Item(2).Value
        let sw = stuff.Item(0).Groups.Item(3).Value
        let resultsLines = results.Split([|'\n'|])
        let foldProg (progs: (string*double*double*double*double) list) (line:string) =
            let tags = line.Split([|','|])
            let progName = tags.[0]
            if (Regex.Match(line, @"^\d\d\d[\S\s]*").Captures.Count > 0) then
                let tagT1 = tags.[1]
                let tagT2 = tags.[2]
                let tagT3 = tags.[6]
                let tagT4 = tags.[7]
                let b1, d1 = Double.TryParse(tagT1)
                let b2, d2 = Double.TryParse(tagT2)
                let b3, d3 = Double.TryParse(tagT3)
                let b4, d4 = Double.TryParse(tagT4)
                if (b1 && b2 && b3 && b4) then
                    System.Console.WriteLine(@"{0} {1} {2} {3} {4} ", tags.[0], tagT1, tagT2, tagT3, tagT4)
                    (progName,double(tagT1),double(tagT2),double(tagT3),double(tagT4))::progs
                else
                    System.Console.WriteLine(@"could noty parse {0} {1}", tags.[0], line)
                    progs
            else
                progs
        let progs = resultsLines |>  Seq.fold foldProg (List.empty<string*double*double*double*double>)
        let getItem (l:string) (item:string) =
            let filterForItem (line:string) =        
                let tags = line.Split([|','|])
                let name = tags.[0].Replace("\"","")
                if (name.Equals(item)) then
                    true
                else
                    false
            let res = l.Split([|'\n'|]) |> Seq.find filterForItem
            res.Substring(res.IndexOf(",")+1).Replace("\"","")
        let createExp (n:string,v1:double,v2:double, v3:double, v4:double) = 
            helper.SaveNewExperiment(dbfile, 
                                    firstCsv, 
                                    getItem hw "CPU Name", 
                                    getItem hw "CPU MHz", 
                                    getItem hw "FPU", 
                                    getItem hw "Memory", 
                                    getItem sw "Operating System", 
                                    getItem sw "Compiler", 
                                    n, 
                                    new decimal(v1), 
                                    new decimal(v2), 
                                    new decimal(v3), 
                                    new decimal(v4), 
                                    cpuspeckind);
        let res = progs |> Seq.iter createExp
        GC.WaitForFullGCComplete() |> ignore
        res


let files = System.IO.Directory.EnumerateFiles(folder + specRawDataSubfolder)
files |> Seq.take 1 |> Seq.iter processFile 

// ----------------- TEST code ----------------
open System

let r = new System.Random()
// the goal if this algorithm is to find the points that better approximate the convex hull

#I @"C:\Users\davidemorelli\AppData\Roaming\Local Libraries\Local Documents\GitHub\Energon\Charts"
#r "MSDN.FSharpChart.dll"
open MSDN.FSharp.Charting

let doAttempt np nb =
    // random points
    let points = Array.init np id |> Array.map (fun _ -> [| r.NextDouble(); r.NextDouble() |])

    // find a basis
    let median = [| points |> Array.averageBy (fun l -> l.[0]) ; points |> Array.averageBy (fun l -> l.[1]) |]
    let distances = points |> Array.mapi (fun i l -> i, Math.Sqrt( Math.Pow(l.[0] - median.[0], 2.0) + Math.Pow(l.[1] - median.[1], 2.0) ))
    let ordereddistances = distances |> Array.sortBy(fun (i,v) -> v) |> Array.rev
    let chosen = ordereddistances |> Seq.take nb |> Seq.toArray
    let chosenpoints = chosen |> Seq.map fst |> Seq.map (fun i -> points.[i]) |> Seq.toArray
    let origin = Seq.init (chosenpoints |> Seq.length) (fun _ ->median) |> Seq.toArray

    // charts
    let totuple (l:float[]) =  l.[0], l.[1]
    let pointchart = points |> Array.map totuple |> FSharpChart.Point
    let medianchart = [| totuple median  |] |>  FSharpChart.Point
    let chosenchart = Seq.zip (chosenpoints |> Array.map totuple) (origin |> Array.map totuple) |> Seq.map (fun (a,b) -> [| a; b |]) |> Seq.concat |> Seq.toArray |>  FSharpChart.Line
    [|  pointchart :> ChartTypes.GenericChart; 
                medianchart  :> ChartTypes.GenericChart;
                chosenchart  :> ChartTypes.GenericChart
            |] |>  FSharpChart.Combine |> FSharpChart.Create


doAttempt 30 4

let drawpoints (points:float[][]) (centers:float[][]) =
    let median = [| points |> Array.averageBy (fun l -> l.[0]) ; points |> Array.averageBy (fun l -> l.[1]) |]
    let totuple (l:float[]) =  l.[0], l.[1]
    let pointchart = points |> Array.map totuple |> FSharpChart.Point
    let medianchart = [| totuple median  |] |>  FSharpChart.Point
    let centerschart = centers |> Array.map totuple |> FSharpChart.Point
    [|  pointchart :> ChartTypes.GenericChart; 
                medianchart  :> ChartTypes.GenericChart;
                centerschart  :> ChartTypes.GenericChart
            |] |>  FSharpChart.Combine |> FSharpChart.Create


let distance l1 l2 =
    Seq.zip l1 l2 |> Seq.sumBy (fun (a,b) -> (b-a)*(b-a)) |> sqrt

let closer (point:float[]) (points:seq<float[]>) =
    let dist, selected = points |> Seq.map (fun p -> distance point p, p) |> Seq.sortBy (fst) |> Seq.head
    selected

let same s1 s2 =
    Seq.forall2 (fun (f1:float) (f2:float) -> f1=f2) s1 s2

let farthest (c:float[]) (points:seq<float[]>) =
    snd (points |> Seq.map (fun p -> distance c p, p) |> Seq.sortBy (fst) |> Seq.toArray |> Array.rev |> Seq.head )

let kmeanStep (centers:seq<float[]>) (points:seq<float[]>) =
    // assign each point to the closer center
    let findCluster = points |> Seq.map (fun p -> closer p centers, p)
    let clusters = findCluster |> Seq.groupBy fst


let points = Array.init 10 id |> Array.map (fun _ -> [| r.NextDouble(); r.NextDouble() |])
let median (points:float[][]) =
    Array.init (points.[0].Length) id |> Array.map (fun i -> points |> Array.map (fun p -> p.[i]) |> Array.average )
let pointsMedian = median points
let centers = [| points.[r.Next(points.Length)]; points.[r.Next(points.Length)]; points.[r.Next(points.Length)] |]
let step = 1
let centers, step = 
    let findCluster = points |> Seq.map (fun p -> closer p centers, p)
    let clusters = findCluster |> Seq.groupBy fst |> Seq.map snd |> Seq.map (fun s -> s |> Seq.map snd)
    drawpoints points centers |> ignore
    let centers = clusters |> Seq.map (fun clust -> farthest pointsMedian clust) |> Seq.toArray
    centers, step+1

let rec kmeansCore n (seeds:float[][]) (points:seq<float array>) =
    if n=0 then
        seeds
    else
        let grouped = points.GroupBy(fun l -> seeds.OrderBy(fun x -> distance x l).First())
        let newseeds = (Seq.map average grouped).ToArray()
        if (Seq.forall2 same seeds newseeds) then
            seeds
        else
            kmeansCore (n-1) newseeds points

let pickRandomElements (l:float[][]) n =
    let dt = DateTime.Now
    let random = new Random(dt.Millisecond + 1000*dt.Second + 60000*dt.Minute)
    let rec pickRandomElement (res:float[][]) (src:float[][]) n =
        if n>0 then
            let idx = random.Next(0, src.Length - 1)
            let chosen = src.ElementAt idx
            let newres = res.Concat( [| chosen |] ).ToArray()
            pickRandomElement newres (src.Where(fun f -> f <> chosen).ToArray()) (n-1)
        else
            res
    let start:float[][] = [| |]
    pickRandomElement start l n

let clusterError (centers:float[][]) (points:float[][]) = 
     let grouped = points.GroupBy(fun l -> centers.OrderBy(fun x -> distance x l).First())        
     grouped.Aggregate(0., fun (sum:float) (element:IGrouping<float[], float[]>) -> sum + element.ToList().Aggregate(0., fun (insum:float) (el:float[]) -> insum + distance (element.Key) el) )

let kmeanstep (points:float[][]) size =
    let seeds = pickRandomElements points size
    let centers = kmeansCore 10 seeds points
    let error = clusterError centers points
    centers, error

let rec kmeans points n =
    let centers, error = kmeanstep points n
    if n > 2 then
        let othercenters, othererror = kmeans points (n-1)
        if (othererror > error) then
            centers, error
        else
            othercenters, othererror
    else
        centers, error



let e n m = (29-n)*(730-m)
let nseq = seq { 3..28 }
let mseq = seq { 30..10..250}

let all = nseq |> Seq.map (fun n -> mseq |> Seq.map (fun m -> e n m) |> Seq.sum) |> Seq.sum
all*100

720*26

e 9 30



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


#I @"C:\Users\davidemorelli\Documents\GitHub\Energon\DataLayer"
#I @"C:\Users\davidemorelli\Documents\GitHub\Energon\DataLayer\bin\Debug"
#I @"C:\Users\davidemorelli\Documents\GitHub\Energon\DataLayer\bin\Debug\x86"
#r @"DataLayer.dll"
#r @"linq2db.dll"
open DataLayer

let dbfile = @"C:\Users\davidemorelli\Documents\GitHub\Energon\DataLayer\SPECCPU.sqlite"

let helper = new SPECCPUHelper()
let folder = @"C:\Data\"    








// ------------------ USE DATA --------------------

let datafolder = @"C:\Users\davidemorelli\Documents\GitHub\Energon\data"

#I @"C:\Users\davidemorelli\Documents\GitHub\Energon\bin\Debug"
#I @"C:\Users\root\Desktop\Energon\bin\Debug"
#I @"C:\Users\davide\Documents\GitHub\Energon\bin\Debug"

#r @"Energon.Measuring.dll"
#r @"Energon.Storage.dll"
#r "System.Data.Linq.dll"

#r "FSharp.Data.TypeProviders.dll"

#r "System.Data.DataSetExtensions.dll"
#r "System.Core.dll"

open Energon.Storage
open System
//open Microsoft.FSharp.Data.TypeProviders
open System.Data.Linq.SqlClient
open System.Linq
open Microsoft.FSharp.Linq
open System.Data.Linq
open Energon.Measuring
open Energon.Measuring.Database
open System.Text
open System.Collections.Generic

// do I want to work on SPEC FP only? INT only? Both?
type subset =
    | Both = 0
    | OnlyINT = 1
    | OnlyFP = 2

let choice = subset.Both

// what is the expected number of programs an environment should have?
// if an environment has less or more we should discard it
let nOfPrograms = match choice with
                    | subset.Both -> 29
                    | subset.OnlyFP -> 17
                    | subset.OnlyINT -> 12
                    | _ -> 0

// TODO: 1 dictionary for programs and one for the testbed
let programNames = new Dictionary<int,string>()
let programPriority = new List<float>(nOfPrograms);
for i in 0..(nOfPrograms - 1) do
    programPriority.Add(0.0)

// ------------------------ SIMILARITY ----------------------
// Functions used to compute similarity of programs

open System

let norm n (a:float[]) =
  Math.Pow(Seq.fold (fun s e -> s + Math.Pow(e, n)) 0.0 a, 1.0/n)

let norm1 (a:float[]) =
  Seq.fold (+) 0.0 a

let norm2 (a:float[]) =
  Math.Sqrt(Seq.fold (fun s e -> s + e * e) 0.0 a)

let cosineSimilarity (a:float[]) (b:float[]) =
  if a.Length <> b.Length then
    raise (new System.Exception("Can not compute cosine similarity of two vectors if they have different dimensionality"))
  let crossProduct = Seq.fold (fun s (ai,bi) -> s + ai * bi) 0.0 (Seq.zip a b)
  let norm_a = norm2 a
  let norm_b = norm2 b
  crossProduct / (norm_a * norm_b)

let angleBetweenVectors a b =
  Math.Acos(cosineSimilarity a b)

// given 2 arrays on N values, it builds N vectors of 2 dimesions, checks the angle between each, and return the larges angle, with indices
// so, given the measures of 2 programs, it will tell you which couple of resources should be used to get the testbed later on
let resourceSimilarity (a:float[]) (b:float[]) =
  let zipped = Array.zip a b
  let mutable maxAngle = 0.0
  let mutable besti = 0
  let mutable bestj = 0
  for i in 0..(zipped.Length - 1) do
    for j in i..(zipped.Length - 1) do
      let a1, b1 = zipped.[i]
      let a2, b2 = zipped.[j]
      let a = [| a1; a2|]
      let b = [| b1; b2|]
      let alpha = angleBetweenVectors (a) (b)
      if alpha > maxAngle then
        maxAngle <- alpha
        besti <- i
        bestj <- j
  (maxAngle, besti, bestj)


#r "GlpkProxy.dll"
open GlpkProxy

let normaliseMeasures (measures:float[][]) =
    let normRow (r:float[]) =
        let max = r |> Array.max
        r |> Array.map (fun m -> m/max)
    measures |> Array.map normRow

// --------------- load data from sqlite ------------ 

open DataLayer

let db = helper.getDB(dbfile)
let envs = db.Environments

// envs |> Seq.length
//let e = envs |> Seq.skip 100 |> Seq.head  // first env

// preparing a dictionary of all programs
let progsDict = new Dictionary<int64, DataModel.Program>()
let progs = helper.getPrograms(db);
progs |> Seq.iter (fun p -> progsDict.Add(p.ID, p))

let orderedProgs = progs.OrderBy(fun p -> p.ID)
for i in 0..(orderedProgs.Count() - 1) do
    programNames.Add(i, orderedProgs.ElementAt(i).Name)

let envsArray = envs |> Seq.toArray

// get all the experiments 
// this will take a while..
let allexps, chosenExps = 
    let getExps (e:DataModel.Environment) = match choice with
                                            | subset.Both -> helper.getExperimentsOfEnvironment(db, e.ID)
                                            | subset.OnlyFP -> helper.getExperimentsOfEnvironmentFilterByKind(db, e.ID, "FP")
                                            | subset.OnlyINT -> helper.getExperimentsOfEnvironmentFilterByKind(db, e.ID, "INT")
                                            | _ -> Array.empty
    let allexps = envsArray |> Array.map getExps
    let chosenExps = allexps |> Seq.filter (fun exps -> Array.length exps = nOfPrograms) |> Seq.cache
    allexps, chosenExps

//allexps  |> Seq.length
//allexps |> Seq.head
//chosenExps |> Seq.length
//chosenExps |> Seq.head

// split the environmnets into valid and invalid environments
let expDict = new Dictionary<int64,Dictionary<int64,decimal>>()
let handleEnv (e:DataModel.Environment) =
    if not (expDict.ContainsKey(e.ID)) then
        expDict.Add(e.ID, new Dictionary<int64,decimal>())
    let dict = expDict.[e.ID]
    let exps = helper.getExperimentsOfEnvironment(db, e.ID)
    let handleExp (exp:DataModel.Experiment) =
        if not (dict.ContainsKey(exp.ID)) then
            dict.Add(exp.ID,exp.PeakRunTime.Value)
        //else 
        //    dict.Add(exp.ID+1000L,exp.BaseRunTime.Value) // TODO: TESTING ONLY
    exps |> Seq.iter handleExp 

envsArray |> Seq.iter handleEnv
let validEnvs = new List<int64>()
let invalidEnvs = new List<int64>()

for e in expDict.Keys do
    let count = expDict.[e].Count
    if count = nOfPrograms then
        validEnvs.Add(e)
    else
        invalidEnvs.Add(e)
        System.Console.WriteLine(System.String.Format("Environment {0} has {1} experiments", e, count))


// validEnvs contains the environment with the correct number of experiments
validEnvs.Count
// validEnvs contains the environment with the incorrect number of experiments
invalidEnvs.Count




// ---------------------------------------------------------------------------------------- 
// This group of instructions will analyse the invalid environment and look for the bias error

let expGroups = db.Experiments.GroupBy(fun (exp:DataModel.Experiment) -> exp.EnvID)
let allExperiments = expGroups |> Seq.map (fun (g) -> int64(g.Key.Value), g |> Seq.toArray)

let TotalEnvironments = expGroups |> Seq.length
let programs = db.Programs.Where(fun _ -> true)
programs |> Seq.length
programs |> Seq.toArray

let SPECINTNames = [|
                    "400.perlbench"
                    "401.bzip2"
                    "403.gcc"
                    "429.mcf"
                    "445.gobmk"
                    "456.hmmer"
                    "458.sjeng"
                    "462.libquantum"
                    "464.h264ref"
                    "471.omnetpp"
                    "473.astar"
                    "483.xalancbmk"
                    |]
let SPECINTPrograms = programs.Where(fun (p:DataModel.Program) -> SPECINTNames.Contains(p.Name)) |> Seq.toArray
let SPECINTProgramsIDs = SPECINTPrograms |> Array.map (fun p -> p.ID)

let experimentsWithSpecInt = allExperiments |> Seq.filter (fun (_,exps) -> exps.Any( fun e -> SPECINTProgramsIDs.Contains(int64(e.ProgID.Value)) )) |> Seq.toArray
let experimentsFilterSpecInt = experimentsWithSpecInt |> Array.map (fun (id, exps) -> id, exps |> Array.filter (fun e -> SPECINTProgramsIDs.Contains(int64(e.ProgID.Value)) ))
experimentsWithSpecInt |> Seq.length
experimentsFilterSpecInt |> Seq.length
let experimentsFilterSpecIntWithCopies =  experimentsFilterSpecInt.Where(fun (i,exps:DataModel.Experiment[]) -> exps.Length > SPECINTPrograms.Length) |> Seq.toArray
let errors = new Dictionary<int64, List<float>>()
for i in SPECINTProgramsIDs do
    errors.Add(i, new List<float>())

SPECINTProgramsIDs |> Array.iter (fun i -> 
        experimentsFilterSpecIntWithCopies |> Array.iter (fun (id,e) ->
            let expi = e |> Seq.filter (fun ex -> int64(ex.ProgID.Value) = i)
            let avg = expi |> Seq.averageBy (fun ex -> ex.BaseRunTime.Value)
            let errs = expi |> Seq.map (fun ex -> (ex.BaseRunTime.Value - avg)/avg ) |> Seq.map (fun d -> float(d))
            errors.[i].AddRange(errs)
        )
    )

let biasErrors = new Dictionary<int64, float>()
for i in SPECINTProgramsIDs do
    let errs = errors.[i]
    let rmse = sqrt( (errs |> Seq.sumBy (fun e -> e*e)) / float(errs |> Seq.length) )
    biasErrors.Add(i, rmse)

let SPECFPPrograms = programs.Where(fun (p:DataModel.Program) -> not (SPECINTNames.Contains(p.Name))) |> Seq.toArray
let SPECFPProgramsIDs = SPECFPPrograms |> Array.map (fun p -> p.ID)    

let experimentsWithSpecFp = allExperiments |> Seq.filter (fun (_,exps) -> exps.Any( fun e -> SPECFPProgramsIDs.Contains(int64(e.ProgID.Value)) )) |> Seq.toArray
experimentsWithSpecFp |> Seq.length
let experimentsFilterSpecFp = experimentsWithSpecFp |> Array.map (fun (id, exps) -> id, exps |> Array.filter (fun e -> SPECFPProgramsIDs.Contains(int64(e.ProgID.Value)) ))
experimentsFilterSpecFp.Count(fun (i,exps) -> exps.Length > SPECFPPrograms.Length)
let experimentsFilterSpecFpWithCopies =  experimentsFilterSpecFp.Where(fun (i,exps:DataModel.Experiment[]) -> exps.Length > SPECFPPrograms.Length) |> Seq.toArray

for i in SPECFPProgramsIDs do
    errors.Add(i, new List<float>())

SPECFPProgramsIDs |> Array.iter (fun i -> 
        experimentsFilterSpecFpWithCopies |> Array.iter (fun (id,e) ->
            let expi = e |> Seq.filter (fun ex -> int64(ex.ProgID.Value) = i)
            let avg = expi |> Seq.averageBy (fun ex -> ex.BaseRunTime.Value)
            let errs = expi |> Seq.map (fun ex -> (ex.BaseRunTime.Value - avg)/avg ) |> Seq.map (fun d -> float(d))
            errors.[i].AddRange(errs)
        )
    )
for i in SPECFPProgramsIDs do
    let errs = errors.[i]
    let rmse = sqrt( (errs |> Seq.sumBy (fun e -> e*e)) / float(errs |> Seq.length) )
    biasErrors.Add(i, rmse)

let allerrors = errors |> Seq.map (fun k -> k.Value) |> Seq.concat 
let biasRMSE = sqrt( (allerrors |> Seq.sumBy (fun e -> e*e)) / float(allerrors |> Seq.length) )

(*
\begin{tabular}{ l c r }
  1 & 2 & 3 \\
  4 & 5 & 6 \\
  7 & 8 & 9 \\
\end{tabular}
*)

// just print a latex table to import results easily in a paper
System.Console.WriteLine(@"\begin{tabular}{ l r }")
System.Console.WriteLine(@"program & RMSE \\")
SPECINTProgramsIDs |> Seq.iter (fun i -> let n = progsDict.[i].Name in let e = biasErrors.[i] in System.Console.WriteLine(System.String.Format(@"{0} & {1} \\", n, e)))
System.Console.WriteLine(@"\hline")
SPECFPProgramsIDs |> Seq.iter (fun i -> let n = progsDict.[i].Name in let e = biasErrors.[i] in System.Console.WriteLine(System.String.Format(@"{0} & {1} \\", n, e)))
System.Console.WriteLine(@"\end{tabular}")
   



// ----------------------------------------------------------------------------------------------
// get the measures from the experiments
// this will build a float[][] matrix that we'll use in our models

let measuresSeq = 
        let doEnv envID =
            let exps = expDict.[envID]
            let sortedExps = exps.Keys.ToArray() |> Array.sort
            let retSeq = sortedExps |> Array.map (fun i -> float(exps.[i]))
            retSeq
        validEnvs |> Seq.map doEnv
let measures = measuresSeq |> Seq.toArray


let orderedNamesOfEnv envID =
        let exps = expDict.[envID]
        let sortedExps = exps.Keys.ToArray() |> Array.sort
        let getName expID= db.Experiments.Where(fun (ex:DataModel.Experiment) -> ex.ID = expID).First()
        let retSeq = sortedExps |> Array.map (fun i -> let e = getName i in e.ProgID.Value)
        retSeq

let refNames = orderedNamesOfEnv (validEnvs |> Seq.head) 
let names = refNames |> Array.map (fun i -> let prog = db.Programs.Where(fun (p:DataModel.Program) -> p.ID=int64(i)).First() in prog.Name)

// check that all programs are the same
// let allNames = validEnvs |> Seq.map orderedNamesOfEnv
// allNames |> Seq.iteri (fun i v -> if (not(Seq.forall2 (fun a b  -> a=b) v refNames)) then Console.WriteLine(@"not OK! index {0}", i))

// we can now close the DB connection
db.Close()

// gets the i-th column: a program
let measuresOfProg (measures:float[][]) i =
    measures |> Seq.map (fun row -> row.[i]) |> Seq.toArray

// the error of a program on a resource (of a certain column and row)
let programError (measured:float) (testbed:float[]) (splitup:float[]) =
    let zip = Array.zip testbed splitup
    let predicted = zip |> Array.fold (fun s (v1,v2) -> s + v1*v2) 0.0
    let error = (predicted - measured)/measured
    error, predicted, measured

// the error of a program on all resources (on all rows)
let programErrors (measured:float[]) (testbed:float[][]) (splitup:float[]) =
    let zip = Array.zip measured testbed
    let errors = zip |>  Array.map (fun (m,t) -> programError m t splitup)
    let onlyErrors = errors |> Array.map (fun (a,_,_) -> a) 
    let average = onlyErrors |> Array.average
    let RMSE = sqrt ((onlyErrors |> (Array.fold (fun s v -> s+v*v) 0.0)) / float(onlyErrors.Length))
    average, RMSE, errors, splitup


// these are the different methods we can use to compute our predictors
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

let estimatedComputationalPatterns = ref 10





// --------------- OLD CODE 

// computes the error of each program
// returns: index of prog, name of prog, average error, std dev err, all errors, splitup
let getProgramErrors (basisT:basisType) (measures_model:float[][]) (measures_test:float[][]) (basis:int[]) (targetIndex:int) =
    let programsIndices = [| targetIndex |] //Array.init (measures_test.[0].Length) (id) |> Array.filter (fun i -> not (basis.Contains(i)))
    let getRow (measures:float[][]) i =
        measures |> Array.map (fun r -> r.[i])
    let filterRows (measures:float[][]) (indices:int[]) =
        let filterRow (r:float[]) =
            r |> Array.mapi (fun i v -> i,v) |> Array.filter (fun (i,v) -> indices.Contains(i)) |> Array.map snd
        measures |> Array.map filterRow
    let testbed_model = filterRows measures_model basis
    let testbed_test =  filterRows measures_test basis
    let programs_model =   filterRows measures_model programsIndices
    let programs_test =   filterRows measures_test programsIndices

    let NNLS (A:DenseMatrix) (b:DenseVector) =
        // see http://books.google.it/books?hl=en&lr=&id=LU5_2sWlVlMC&oi=fnd&pg=PP2&ots=x2kEt5s5kG&sig=HbeDhVWlooj91jYrD8pR9k5mzLk&redir_esc=y#v=onepage&q&f=false
        // pag 161
        let n = A.ColumnCount
        // step 1
        let P = []
        let Z = [0..(n-1)]
        let checkIter iter =
            if (iter < 0) then
                System.Console.WriteLine("infinite loop detected!")
                System.Console.WriteLine(A.ToMatrixString(A.RowCount, A.ColumnCount))
                System.Console.WriteLine(b.ToVectorString(300,300))
                raise (Exception("out of iterations n=" + n.ToString() + " " + testbed_model.Length.ToString() + " " + testbed_test.Length.ToString() + " " + programs_model.Length.ToString() + " " + programs_test.Length.ToString()))

        let steps2to5 (x:DenseVector) (z:DenseVector) (P:int list) (Z:int list) f iter =
            checkIter iter
            // step 2
            let w = A.Transpose().Multiply(b - A.Multiply(x))
            // step 3
            if (Z.IsEmpty || Z |> List.map (fun j -> w.Item(j) <= 0.0) |> List.forall (id)) then
                //System.Console.WriteLine("solved in " + iter.ToString() + " steps" )
                x
            else
                // step 4
                let t,max = Z |> List.map (fun j -> j, w.Item(j)) |> List.maxBy (fun (j,v) -> v)
                // step 5
                let P2 = t::P
                let Z2 = Z |> List.filter (fun j -> j <> t)
                f x z P2 Z2 (iter-1)

        let rec steps6to11 (x:DenseVector) (z:DenseVector) (P:int list) (Z:int list) iter =
            checkIter iter
            // step 6
            let Ap = DenseMatrix.ofColumnVectors( P |> List.map (fun j -> A.Column(j)) )
            let zp = Ap.QR().Solve(b)
            let z = DenseVector.zeroCreate(n)
            P |> List.iteri (fun i v -> z.Item(v) <- zp.Item(i) )
            // step 7
            if (P |> List.map (fun j -> z.Item(j) > 0.0) |> List.forall (id)) then
                //printf "go to step 2\n"
                // iterate
                steps2to5 z z P Z steps6to11 (iter - 1)
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
                steps6to11 (DenseVector.OfVector(x)) (DenseVector.OfVector(z)) P2 Z2 (iter - 1)

        steps2to5 (DenseVector.zeroCreate(n)) (DenseVector.zeroCreate(n)) P Z steps6to11 10000

    let NNLS2 (A:float[][]) (b:float[]) =
        let A2 = DenseMatrix.OfRowsCovariant(A.Count(), A.[0].Count(), A)
        let b2 = DenseVector.ofList (b |> Array.toList)
        let x = NNLS A2 b2
        x.AsEnumerable() |> Seq.toArray

    let r = new System.Random()
    match basisT with
    | basisType.NNLS ->
        //let X = DenseMatrix.OfRowsCovariant(testbed_model.Length, testbed_model.[0].Length, testbed_model)
        let handleProg (i:int) =
            let model = getRow programs_model i
            let test = getRow programs_test i
            let name = programNames.[programsIndices.[i]]
            let idx = programsIndices.[i]
            //let splitup = X.Svd(true).Solve(new DenseVector(model)) |> Seq.toArray
            let splitup = NNLS2 testbed_model model
            let a,d, e, s = programErrors test testbed_test splitup
            idx, name, a, d, e, s
        // pick a program of the availables and test
        let res = handleProg 0
        [| res |]
    | basisType.NNMF ->
        let NMF (v:DenseMatrix) pc =
            let costF (A:DenseMatrix) (B:DenseMatrix) =
                let C = A.Subtract(B)
                seq {
                    for i in 0..(C.RowCount-1) do
                        for j in 0..(C.ColumnCount-1) do
                            yield C.Item(i,j)
                    } |> Seq.map (fun v -> v*v) |> Seq.sum
            let r = new ContinuousUniform(0.0, 1.0)
            let ic = v.RowCount    
            let fc = v.ColumnCount
            let w = DenseMatrix.CreateRandom(ic, pc, r)
            let h = DenseMatrix.CreateRandom(pc, fc, r)
            let epsilon = 0.000001
            let rec factorize (v:DenseMatrix) (h:DenseMatrix) (w:DenseMatrix) iter =
                let wh = w.Multiply(h)
                let cost = costF v (DenseMatrix.OfMatrix(wh))
                if (cost<epsilon || iter = 0) then
                    h,w
                else
                    let hn = w.Transpose().Multiply(v)
                    let hd = w.Transpose().Multiply(w).Multiply(h)
                    let h_cols = h.ToColumnWiseArray()
                    let hn_cols = hn.ToColumnWiseArray()
                    let hd_cols = hd.ToColumnWiseArray()
                    let newh_cols = Array.mapi (fun i v -> v*hn_cols.[i]/hd_cols.[i]) h_cols
                    let newh = DenseMatrix.OfColumnMajor(h.RowCount, h.ColumnCount, newh_cols )
                    let wn = v.Multiply(newh.Transpose())
                    let wd = w.Multiply(newh.Multiply(newh.Transpose()))
                    let w_cols = w.ToColumnWiseArray()
                    let wn_cols = wn.ToColumnWiseArray()
                    let wd_cols = wd.ToColumnWiseArray()
                    let neww_cols = Array.mapi (fun i v -> v*wn_cols.[i]/wd_cols.[i]) w_cols
                    let neww = DenseMatrix.OfColumnMajor(w.RowCount, w.ColumnCount, neww_cols )
                    factorize v newh neww (iter-1)
            let h,w = factorize v h w 50
            let cost = costF v (DenseMatrix.OfMatrix(w.Multiply(h)))
            h,w,cost
        let predictNMF (H:DenseMatrix) (W:DenseMatrix) (b:DenseVector) (a:DenseVector) =
            //let w = H.Transpose().Svd(true).Solve(a)
            let w = NNLS (DenseMatrix.OfMatrix(H.Transpose())) a
            //let h = W.Svd(true).Solve(b)
            let h = NNLS W b
            let prev = h.ToRowMatrix().Multiply(w)
            prev.Item(0)
        let A = DenseMatrix.OfRowsCovariant(testbed_model.Length, testbed_model.[0].Length, testbed_model)
        let targetProg = r.Next(0, programs_model.[0].Length)
        let H,W,c = NMF A (!estimatedComputationalPatterns)
        let b = DenseVector.ofSeq(getRow programs_model targetProg)
        let handleResource i =
            let name = programNames.[programsIndices.[targetProg]]
            let idx = programsIndices.[targetProg]
            let a = testbed_test.[i]
            let predicted = predictNMF H W b (DenseVector.ofSeq a)
            let measured = programs_test.[i].[targetProg]
            let err = (predicted-measured)/measured
            idx, name, err, 0.0, [| err,predicted,measured |], [| 0.0 |]
        Array.init (testbed_test.Length) (id) |>  Array.map (fun i -> handleResource i)
       

    | basisType.cone ->
        let s = new SplitupFinder()
        let programs = Array.init (basis.Length) (id) |> Array.map (getRow testbed_model) |> Array.map (fun r -> 
                let p = new Program()
                p.Measures <- r
                p
            )
        s.Testbed <- programs
        let handleProg (i:int) =
            let model = getRow programs_model i
            let test = getRow programs_test i
            let name = programNames.[programsIndices.[i]]
            let idx = programsIndices.[i]
            let p = new Program()
            p.Measures <- model
            s.Target <- p
            if (s.FindSplitup(true)) then
                let splitup = s.Splitup
                let a,d, e, s = programErrors test testbed_test splitup
                idx, name, a, d, e, s
            else
                System.Console.WriteLine("could not find a splitup for program {0} {1}", i, name)
                idx, name, 0.0, 0.0, [| |], [| |]
        // pick a program of the availables and test
        let res = handleProg 0
        [| res |]
    | basisType.gauss ->
        //let testbedAsIenum = testbed_model |> Array.map (fun row -> new MathNet.Numerics.LinearAlgebra.Double.DenseVector(row) :>  MathNet.Numerics.LinearAlgebra.Double.Vector)
        let X = DenseMatrix.OfRowsCovariant(testbed_model.Length, testbed_model.[0].Length, testbed_model)
        let handleProg (i:int) =
            let model = getRow programs_model i
            let test = getRow programs_test i
            let name = programNames.[programsIndices.[i]]
            let idx = programsIndices.[i]
            let splitup = X.Svd(true).Solve(new DenseVector(model)) |> Seq.toArray
            let a,d, e, s = programErrors test testbed_test splitup
            idx, name, a, d, e, s
        // pick a program of the availables and test
        let res = handleProg 0
        [| res |]
    | basisType.tls ->
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
        let handleProg (i:int) =
            let model = getRow programs_model i
            let test = getRow programs_test i
            let name = programNames.[programsIndices.[i]]
            let idx = programsIndices.[i]
            let splitup = TotalLeastSquare testbed_model model
            let a,d, e, s = programErrors test testbed_test splitup
            idx, name, a, d, e, s
        // pick a program of the availables and test
        let res = handleProg 0
        [| res |]

// ------------ now analyse data ---------
// convex hull
#I @"C:\Users\davidemorelli\AppData\Roaming\Local Libraries\Local Documents\GitHub\Energon\Debug"
#r "MIConvexHullPlugin.dll"

#I @"C:\Users\davidemorelli\Documents\GitHub\Energon\packages\MathNet.Numerics.FSharp.2.6.0\lib\net40"
#I @"C:\Users\davidemorelli\Documents\GitHub\Energon\packages\MathNet.Numerics.2.6.2\lib\net40"
#r "MathNet.Numerics.FSharp.dll"
#r "MathNet.Numerics.dll"
 
open MathNet.Numerics
open MathNet.Numerics.LinearAlgebra.Double
open MathNet.Numerics.Distributions
open MathNet.Numerics.Statistics

#r @"C:\Users\davidemorelli\Documents\GitHub\Energon\Solvers\bin\Debug\Solvers.dll"
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

let values_array =  measures

let valuesSequence = Seq.init (values_array.Length) (fun i -> values_array.[i] |> Array.toSeq)
let M = DenseMatrix.OfRows(values_array.Length, values_array.[0].Length, valuesSequence).NormalizeRows(2).Transpose()

let testSize = 1

let runTest print (basisT:basisType) modelSize desiredBasisSize targetProgram =
    let r = new System.Random()
    //let targetProgram = r.Next(0, values_array.[0].Length)
    // split the measures into separate sets for model and test
    let values_model, values_test = 
        //let chunkSize = values_array.Length / modelSize
        //let indices = Array.init (modelSize) (fun i -> i*chunkSize + int(r.NextDouble()*float(chunkSize)))
        let indices = Seq.init (values_array.Length) (fun i -> i,r.NextDouble()) |> Seq.sortBy (fun (i,v) -> v) |> Seq.take (modelSize + testSize) |> Seq.map fst |> Seq.toArray
        //let indices = [| |]
        //printf "%i %i %i %i %i ...\n" (indices.[0]) (indices.[1]) (indices.[2]) (indices.[3]) (indices.[4])
        //let wIndices = values_array |> Array.mapi (fun i r -> i,r)
        let model = indices |> Seq.take modelSize |> Seq.toArray |> Array.map (fun i -> values_array.[i])
        let test = indices |> Seq.skip modelSize |> Seq.toArray |> Array.map (fun i -> values_array.[i])
        //let model = wIndices |> Array.filter (fun (i,r) -> indices.Contains(i)) |> Array.map snd
        normaliseMeasures model, test

    // computing the similarity matrix of programs
    let nOfPrograms = Seq.length values_array.[0]
    let listOfIndices = List.init nOfPrograms (fun i -> i)
    let similarityMatrix = Array2D.create nOfPrograms nOfPrograms 0.0
    for i in 0..(nOfPrograms - 1) do
        let a = measuresOfProg values_model i
        for j in 0..(nOfPrograms - 1) do
            let b = measuresOfProg values_model j
            similarityMatrix.[i,j] <- cosineSimilarity a b

    // print the similarity matrix as a ascii table for gnuplot
    if (print) then
        let sb = new StringBuilder()
        for i in 0..(nOfPrograms - 1) do
            for j in 0..(nOfPrograms - 1) do
                let sim = similarityMatrix.[i,j]
                sb.AppendFormat("{0} ", sim)  |> ignore
            sb.AppendLine("")  |> ignore
        System.IO.File.WriteAllText(folder + "correlation.txt", sb.ToString())    

    let rec measureSimilarity (attempt:int[]) =
        if attempt.Length = 2 then
            similarityMatrix.[attempt.[0], attempt.[1]]
        else
            let a = attempt.[0]
            let sum = attempt |> Seq.skip 1 |> Seq.sumBy (fun b -> similarityMatrix.[a,b])
            sum + measureSimilarity (attempt |> Seq.skip 1 |> Seq.toArray)


    // normalize 
    let normalise f a =
        let n:float = f a
        a |> Array.map (fun i -> i / n)
    let normalise2 = normalise norm2
    let normalise1 = normalise norm1
    let normalise05 = normalise (norm 0.5)
    let normf = normalise1

    let non_normalised_points measure_model = 
        let getIth i = measure_model |> Array.map (fun (l:float[]) -> l.[i])
        let indices = Array.init (measure_model.[0].Length) (id)
        indices |> Array.map getIth 

    let normalised_measure_model measure_model = 
        let getIth i = measure_model |> Array.map (fun (l:float[]) -> l.[i])
        let indices = Array.init (measure_model.[0].Length) (id)
        indices |> Array.map getIth |> Array.map normf

    let normalised_points = normalised_measure_model values_model
    // remove 1 dimension to avoid singularities (known issue of MIConvexHull)
    let points = normalised_points |> Array.map (fun (point:float[]) -> point |> Seq.skip 1 |> Seq.toArray )

    (*
    let basis = 
        match basisT with
        | basisType.cone ->
            // run the convex hull alg, but not including the target program
            let pointsWithoutTarget = points |> Array.mapi (fun i v -> i,v) |> Array.filter (fun (i,v) -> not (i=targetProgram)) |> Array.map (fun (i,v) -> v)
            let hull = MIConvexHull.ConvexHull.Create(pointsWithoutTarget)
            let hull_points = hull.Points
            let hull_floats = hull_points |> Seq.map (fun p -> p.Position) |> Seq.toArray
            
            let printPoints4Gnuplot (points:float[][]) filename=
                let sb = new System.Text.StringBuilder()
                points |> Array.iter (fun p -> 
                        p |> Array.iter (fun v -> sb.AppendFormat("{0} ", v)  |> ignore )
                        sb.AppendLine() |> ignore
                    )
                System.IO.File.WriteAllText(folder + filename, sb.ToString())

            let printPoints4Grapher (points:float[][]) filename=
                let sb = new System.Text.StringBuilder()
                points |> Array.iter (fun p -> 
                        p |> Array.iter (fun v -> sb.AppendFormat("{0},", v)  |> ignore )
                        sb.Remove(sb.Length - 1, 1) |> ignore
                        sb.AppendLine() |> ignore
                    )
                System.IO.File.WriteAllText(folder + filename, sb.ToString())

            if (print) then
                printPoints4Gnuplot points "PointsAll.dat"
                printPoints4Gnuplot hull_floats "PointsHull.dat"
                printPoints4Gnuplot (non_normalised_points values_model) "PointsNonNormalised.dat"

                printPoints4Grapher points "PointsAll.txt"
                printPoints4Grapher hull_floats "PointsHull.txt"
                printPoints4Grapher (non_normalised_points values_model) "PointsNonNormalised.txt"

            let findProg r =
                let same a =
                    Seq.forall2 (fun v w -> v = w) a r
                points |> Seq.findIndex same

            let basis = hull_points |> Seq.map (fun p -> p.Position) |>  Seq.map findProg |> Seq.toArray |> Array.sort
            basis
            // TODO: do mesh simplification to desiredBasisSize
        | basisType.gauss | basisType.tls | basisType.NNLS | basisType.NNMF ->
            // TODO find the 'more' ortogonal..
            //[| 11; 16; 21; 2; 23; 4 |]
            let rec findbasis (moretogo:int) (currentBasis:int list) =
                if moretogo = 0 then
                    currentBasis
                else 
                    // find the indices that are not already in the basis
                    let validIndices = Array.init (similarityMatrix.GetLength(0) ) (id) |> Array.filter (fun i -> not(currentBasis.Contains(i)) ) |> Array.filter (fun i -> not (i = targetProgram))
                    // for each program not in the basis, compute the sum of correlations with the other programs NOT in the basis
                    // then take the lower
                    let winner = validIndices |> Array.map (fun i -> i, validIndices |> Seq.map (fun j -> similarityMatrix.[i,j]) |> Seq.sum ) |> Seq.sortBy (snd) |> Seq.map (fst) (*|> Seq.toArray |> Array.rev*) |> Seq.head
                    findbasis (moretogo - 1) (winner::currentBasis)
            let res = findbasis desiredBasisSize []
            List.toArray res
    *)
    let findBasis2 (basisT:basisType) (values_array:float[][]) basisSize =
        let allowed = Array.init (values_array.[0].Length) (id) |> Array.map (fun i -> not (i = targetProgram))
        let values_array = values_array |> Array.map (fun row -> row |> Array.mapi (fun i v -> if allowed.[i] then Some v else None )  |> Array.choose (id) )
        let valuesSequence = Seq.init (values_array.Length) (fun i -> values_array.[i] |> Array.toSeq)
        let M = DenseMatrix.OfRows(values_array.Length, values_array.[0].Length, valuesSequence ).NormalizeRows(2).Transpose()
        let basis, _,_,_ = findBasis (basisT) (DenseMatrix.OfMatrix(M)) basisSize
        let mapIndex i = if i < targetProgram then i else i+1
        basis |> Array.map mapIndex


    let basis = findBasis2 basisT normalised_points desiredBasisSize

    let res = getProgramErrors basisT values_model values_test basis targetProgram
    let averages = 
        let printSplitup (data:(string*float[])[]) =
            let sb = new System.Text.StringBuilder()
            data |> Array.iter (fun (n,predictors) -> 
                        sb.AppendFormat("{0} ", n) |> ignore
                        predictors |> Array.iter (fun v -> sb.AppendFormat("{0} ", v)  |> ignore )
                        sb.Remove(sb.Length - 1, 1) |> ignore
                        sb.AppendLine() |> ignore
                    )
            let filename = System.String.Format("predictors_{0}_{1}_{2}.dat", basisTypeToString basisT, modelSize, desiredBasisSize)
            System.IO.File.WriteAllText(folder + filename, sb.ToString())
        let printProgramsErrors (data:(string*float*float)[]) =
            let sb = new System.Text.StringBuilder()
            data |> Array.iter (fun (n,avg,RMSE) -> 
                        sb.AppendFormat("{0},{1},{2}", n,avg,RMSE) |> ignore
                        sb.AppendLine() |> ignore
                    )
            let filename = System.String.Format("programs_errors_{0}_{1}_{2}.dat", basisTypeToString basisT, modelSize, desiredBasisSize)
            System.IO.File.WriteAllText(folder + filename, sb.ToString())        
        //let a = res |> Array.map (fun (i,n,a,d,e,s) -> a) |> Array.average
        //let d = res |> Array.map (fun (i,n,a,d,e,s) -> d) |> Array.average
        //let mse = res |> Array.map (fun (i,n,a,d,e,s) -> e) |> Array.concat |> Array.map (fun (v,_,_) -> v*v) |> Array.sum
        //let count = res |> Array.map (fun (i,n,a,d,e,s) -> e) |> Array.concat |> Array.length
        let splitups = res |> Array.map (fun (i,n,a,d,e,s) -> s) 
        let names_splitups = res |> Array.map (fun (i,n,a,d,e,s) -> n,s)
        let names_errors = res |> Array.map (fun (i,n,a,d,e,s) -> n,a,d)
        let errors = res |> Array.map  (fun (i,n,a,d,e,s) -> e) |> Array.concat |> Array.map (fun (a,b,c) -> a)
        let a = errors |> Array.average
        let rmse = errors |> Array.map (fun v -> v*v) |> Array.average |> sqrt
        if (print) then
            printSplitup names_splitups
            printProgramsErrors names_errors
        a,rmse,splitups,errors

    averages, res, basis, values_model, values_test, basis.Length, points


let runRandomTest print basistype modelsize basisize =
    let r = new System.Random()
    runTest print basistype modelsize basisize (r.Next(0, values_array.[0].Length))

let runAll  print basistype modelsize basisize =
    Array.init 29 (id) |> Array.map (fun i -> 
        let prog =  Array.init (30) (id) |> Array.map (fun _ -> runTest  print basistype modelsize basisize i)
        let sample = prog.[0]
        let (_, res, basis, _, _, _, _) = sample
        let idx, name, avg,stddev,errorsTouple,_ = res.[0]
        let errorsTmp = prog |> Array.map (fun sample ->
                let (_, res, _, _, _, _, _) = sample
                let _, _, _,_,errorsTouple,_ = res.[0]
                let errs = errorsTouple |> Array.map (fun (v,_,_) -> v)
                errs
            )
        let errors = errorsTmp |> Array.concat
        let avg = errors |> Array.average
        let stddev = errors |> Array.map (fun v -> v-avg) |> Array.map (fun v -> v*v) |> Array.average |> sqrt
        let rmse =  errors  |> Array.map (fun v -> v*v) |> Array.average |> sqrt
        name, avg, stddev, rmse, errors
        )

let res = runAll false basisType.NNLS 50 25
res |> Array.iter (fun (name,avg,stddev,rmse,_) -> System.Console.WriteLine("{0} {1} {2} {3}", name, avg, stddev, rmse ) )

let (averages), res, basis, values_model, values_test, n, p = runTest false basisType.NNMF 250 25 0
let (averages), res, basis, values_model, values_test, n, p = runTest false basisType.NNLS 50 20 4
let (averages), res, basis, values_model, values_test, n, p = runTest false basisType.tls 50 10 4
let (averages), res, basis, values_model, values_test, n, p = runTest false basisType.gauss 50 20 0

// run 1
//let averages, res, basis, values_model, values_test, n, p = runTest true basisType.cone 5 5 
//let (averages), res, basis, values_model, values_test, n, p = runTest true basisType.gauss 30 9
estimatedComputationalPatterns := 5

let (averages), res, basis, values_model, values_test, n, p = runRandomTest true basisType.gauss 30 10
let (averages), res, basis, values_model, values_test, n, p = runRandomTest true basisType.NNMF 50 20
let (averages), res, basis, values_model, values_test, n, p = runRandomTest false basisType.NNMF 50 20

let (averages), res, basis, values_model, values_test, n, p = runTest false basisType.NNMF 50 20 0

let (averages), res, basis, values_model, values_test, n, p = runRandomTest false basisType.gauss 80 22

//let (avg,rmse,splitups,errors), res, basis, values_model, values_test, n, p = runTest false basisType.gauss 30 9
//let (avg,rmse,splitups,errors), res, basis, values_model, values_test, n, p = runTest false basisType.NNLS 200 10

//let measureTime =
//    let start = System.DateTime.Now
//    let (avg,rmse,splitups,errors), res, basis, values_model, values_test, n, p = runTest false basisType.NNLS 200 28
//    System.DateTime.Now.Subtract(start).TotalMilliseconds


//let averages, res, basis, values_model, values_test, n, p = runTest true basisType.gauss 30 9
//let averages2, res2, basis2, values_model2, values_test2, n2, p2 = runTest true basisType.cone 4 4

let printBasis (basisT:basisType) (modelSize:int) basis =
    let sb = new System.Text.StringBuilder()
    let conestring = basisTypeToString basisT 
    basis |> Seq.iter (fun i -> sb.AppendLine(programNames.[i]) |> ignore)
    let filename = System.String.Format("{0}basis_{1}_{2}_{3}.tex", folder, conestring, modelSize, basis |> Seq.length)
    System.IO.File.WriteAllText(filename, sb.ToString())

let printNonBasis (basisT:basisType) (modelSize:int) (basis:int[]) =
    let sb = new System.Text.StringBuilder()
    let conestring = basisTypeToString basisT 
    Array.init (nOfPrograms) (id) |> Array.filter (fun i -> not (basis.Contains(i))) |> Seq.iter (fun i -> sb.AppendLine(programNames.[i].Replace(".", "_")) |> ignore)
    let filename = System.String.Format("{0}programs_{1}_{2}_{3}.tex", folder, conestring, modelSize, basis |> Seq.length)
    System.IO.File.WriteAllText(filename, sb.ToString())

printBasis basisType.gauss 30 basis
printNonBasis basisType.gauss 30 basis

printBasis basisType.cone 4 basis2
printNonBasis basisType.cone 4 basis2

res |> Seq.iter (fun (i, n, a, d, _, _ ) -> System.Console.WriteLine(System.String.Format("{0} average={1} stdDev={2}", n, a, d)))

let printProgramErrDetail (basisT:basisType) modelSize basisSize (i:int, name:string, avg:float, rmse:float, errors:(float*float*float)[], splitups:float[]) =
    let sb = new System.Text.StringBuilder()
    let onlyErrors = errors |> Array.map (fun (a,_,_) -> a)
    onlyErrors |> Seq.iter (fun v -> sb.AppendLine(System.String.Format("{0}",v)) |> ignore)
    let conestring = basisTypeToString basisT  
    let filename = System.String.Format("{0}{1}_{2}_{3}_{4}.dat", folder, name.Replace(".", "_"), conestring, modelSize, basisSize)
    System.IO.File.WriteAllText(filename, sb.ToString())
    let dataForScatter = errors |> Array.map (fun (_,a,b) -> a,b)
    let sb2 = new System.Text.StringBuilder()
    dataForScatter |> Seq.iter (fun (x,y) -> sb2.AppendLine(System.String.Format("{0} {1}",x, y)) |> ignore)
    let filename2 = System.String.Format("{0}{1}_{2}_{3}_{4}_scatter.dat", folder, name.Replace(".", "_"), conestring, modelSize, basisSize)
    System.IO.File.WriteAllText(filename2, sb2.ToString())
    //let sb3 = new System.Text.StringBuilder()
    //let filename3 = System.String.Format("{0}{1}_{2}_{3}_{4}_predictors.dat", folder, name.Replace(".", "_"), conestring, modelSize, basisSize)
    //splitups |> Seq.iter (fun (x) -> sb2.AppendLine(System.String.Format("{0} {1}",x, y)) |> ignore)
    //System.IO.File.WriteAllText(filename3, sb3.ToString())

res |> Seq.iter (printProgramErrDetail basisType.gauss 30 9)
res2 |> Seq.iter (printProgramErrDetail basisType.cone 4 (basis2.Length))

// iterate a specific case "iter" times to get statistical significance
let iterate basisType iter modelSize basisSize = 
    let res = Array.init iter (id) |> Array.map (fun _ ->
        let rec foo () =
            try
                let (avg,rmse,splitups,errors), res, basis, values_model, values_test, n, p = 
                    runRandomTest false basisType modelSize basisSize
                let avg = errors |> Array.average
                let rmse = sqrt((errors |> Array.map (fun v -> v*v) |> Array.sum)/float(errors.Length))
                avg,rmse, errors
            with
                | :? _ -> printf "infinite loop detected!\n"; foo ()
        foo ()
                ) 
    let getAverageStdDev ary = 
        let average_ary = ary  |> Array.average
        let stdDev_ary = sqrt(( ary |> Array.map (fun v -> v - average_ary) |> Array.map (fun v -> v*v) |> Array.sum ) / (float(ary.Length)))
        average_ary, stdDev_ary
    let errors = res |> Array.map (fun (a,b,c) -> c) |> Array.concat
    //let average_average, average_stddev = getAverageStdDev (res |> Array.map (fun (a,b,c) -> a))
    let rmse = sqrt((errors |> Array.map (fun v -> v*v) |> Array.sum)/float(errors.Length))
    let average, stddev = getAverageStdDev errors
    average, stddev, rmse, errors

// try 1
let average, stddev, rmse, _ = iterate basisType.gauss 1 50 25
let average, stddev, rmse, _ = iterate basisType.cone 30 50 10
let average, stddev, rmse, _ = iterate basisType.NNMF 30 100 25
estimatedComputationalPatterns := 5

(*
// write names
let sb = new System.Text.StringBuilder()
names |> Array.iter (fun n -> sb.AppendFormat(@"{0}",n) ; sb.AppendLine() |> ignore)
let filename = System.String.Format("{0}names.dat", folder)
System.IO.File.WriteAllText(filename, sb.ToString())
*)

open System.Threading

let stop = ref false


let printBatchOfRMSEAsynch (basisT:basisType) samplesize =
    new Thread(fun () -> 
            let conestring = basisTypeToString basisT
            let modelSizes = Array.init (20) (fun i -> 20 + i*10)
            let basisSizes = Array.init (28) (fun i -> 1 + i)
            let filename = System.String.Format("{0}RMSE_{1}_All_summary_sampleSize{2}.dat", folder, conestring, samplesize)
            let sb = new System.Text.StringBuilder()
            sb.Append(@"#modelsize basissize RMSD")
            let header a b =
                names |> Array.iter (fun n -> sb.AppendFormat(@" {0}_{1}_{2}", n, a, b) |> ignore)
            header "RMSD" ""
            header "0.0" "0.05"
            header "0.05" "0.1"
            header "0.1" "0.2"
            header "0.2" "0.5"
            header "0.5" "999"
            sb.AppendLine()

            modelSizes |> Array.iter (fun size -> 
                    basisSizes |> Array.iter (fun basis ->
                        let runprog p = 
                            if (!stop) then raise (Exception("ABORT"))
                            let name = names.[p]
                            let runOne (_) =
                                let (averages), res, basisVector, values_model, values_test, n, _ = runTest false basisT size basis p
                                let _,_,_,errors = averages
                                errors
                            let errors = Array.init (samplesize) runOne |> Array.concat
                            let sum = errors |> Array.sumBy (fun v -> v*v)
                            let rmsd = sqrt(sum / float(Array.length errors) )
                            let sb2 = new System.Text.StringBuilder()
                            errors |> Seq.iter (fun v -> sb2.AppendLine(System.String.Format("{0}",v)) |> ignore)
                            let conestring = basisTypeToString basisT  
                            let filename = System.String.Format("{0}{1}_{2}_{3}_{4}.dat", folder, name.Replace(".", "_"), conestring, size, basis)
                            System.IO.File.WriteAllText(filename, sb2.ToString())
                            errors
                        let programsError =  Array.init (values_array.[0].Length) runprog
                        let programsRmsd = programsError |> Array.map (fun vec -> let sum = vec |> Array.sumBy (fun v -> v*v) in sqrt(sum/float(vec |> Array.length)))
                        let percBetween a b =
                            programsError |> Array.map (fun vec -> let count =  vec |> Array.map (fun v -> Math.Abs(v) ) |> Array.filter (fun v -> a<=v && v<b) |> Array.length in float(count)/float(vec |> Array.length) )
                        let percBetween000_005 = percBetween 0.0 0.05
                        let percBetween005_010 = percBetween 0.05 0.1 
                        let percBetween010_020 = percBetween 0.1 0.2
                        let percBetween020_050 = percBetween 0.2 0.5
                        let percBetween050_999 = percBetween 0.5 999.9

                        let errors = programsError |> Array.concat
                        let sum = errors |> Array.sumBy (fun v -> v*v)
                        let rmsd = sqrt(sum / float(Array.length errors) )
                        
                        sb.AppendFormat(System.String.Format("{0} {1} {2}", size, basis, rmsd)) |> ignore
                        let printArray (ar:float[]) =
                            ar |> Array.iter (fun v -> sb.AppendFormat(@" {0}", v) |> ignore )
                        printArray programsRmsd
                        printArray percBetween000_005
                        printArray percBetween005_010
                        printArray percBetween010_020
                        printArray percBetween020_050
                        printArray percBetween050_999
                        sb.AppendLine()
                        // feedback to console
                        System.Console.WriteLine(System.String.Format("{0} {1} {2} {3}", conestring, size, basis, rmsd)) 
                    )
                )
            //System.Console.WriteLine(sb.ToString())
            System.IO.File.WriteAllText(filename, sb.ToString())
            System.Console.WriteLine("RMSE file written, all done")
        )

stop := false
let t1 = printBatchOfRMSEAsynch (basisType.gauss) 30
t1.Start()
stop := true

names

let programsError = [| [| 0.0; 0.01; 0.11 |]; [|0.11; -0.25; 0.51 |] |]
let percBetween a b =
    programsError |> Array.map (fun vec -> let count =  vec |> Array.map (fun v -> Math.Abs(v) ) |> Array.filter (fun v -> a<=v && v<b) |> Array.length in float(count)/float(vec |> Array.length) )
let percBetween000_005 = percBetween 0.0 0.05
let percBetween005_010 = percBetween 0.05 0.1 
let percBetween010_020 = percBetween 0.1 0.2
let percBetween020_050 = percBetween 0.2 0.5
let percBetween050_999 = percBetween 0.5 999.9


let printBatchOfRMSE2Asynch (basisT:basisType) samplesize =
    new Thread(fun () -> 
            let sb = new System.Text.StringBuilder()
            let conestring = basisTypeToString basisT
            let modelSizes = Array.init (20) (fun i -> 20 + i*10)
            let basisSizes = Array.init (28) (fun i -> 1 + i)
            let filename = System.String.Format("{0}RMSE_{1}_All_summary_sampleSize{2}.dat", folder, conestring, samplesize)
            modelSizes |> Array.iter (fun size -> 
                    basisSizes |> Array.iter (fun basis ->
                        if (!stop) then raise (Exception("ABORT"))
                        //printf "model %i basis %i\n" size basis
                        //let average_average, average_stddev, RMSE_average, RMSE_stddev = 0.0, 0.0, 0.0, 0.0
                        let average_average, average_stddev, RMSE, errors = iterate basisT samplesize size basis
                        sb.AppendLine(System.String.Format("{0} {1} {2} {3} {4}", size, basis, average_average, average_stddev, RMSE)) |> ignore
                        // feedback to console
                        System.Console.WriteLine(System.String.Format("{0} {1} {2} {3} {4} {5}", conestring, size, basis, average_average, average_stddev, RMSE)) 
                    )
                )
            //System.Console.WriteLine(sb.ToString())
            System.IO.File.WriteAllText(filename, sb.ToString())
            System.Console.WriteLine("RMSE file written, all done")
        )
stop := false
let t1 = printBatchOfRMSE2Asynch (basisType.gauss) 300
t1.Start()
let t2 = printBatchOfRMSE2Asynch (basisType.NNLS) 300
t2.Start()
let t3 = printBatchOfRMSE2Asynch (basisType.NNMF) 100
t3.Start()
let t3 = printBatchOfRMSE3Asynch (basisType.NNMF) 30
t3.Start()
stop := true

estimatedComputationalPatterns := 5


// TODO cose da provare
// quando cerchi decomposizione, fallo piu'  volte e simula con i dati a disposizione (leave 1 out), scegli quello che funziona meglio

// TODO: per ogni problema trova il pc che minimizza errore

// TODO: c'e'  un modo di predevere quale solver e'  piu'  adatto al caso specifico?

// TODO: kalmann o idee simili a kalmann: raffinare adattivamente

// TODO: regression tree

// TODO: prima fai PCA sulle misure..

//TODO: per trovare la base fai PCA, poi clustering e usa 1 surrogato per cluster (kmean)

// TODO: code signatures & performance prediction, usa F# leggi http://cseweb.ucsd.edu/users/calder/papers/ISPASS-05-Strong-Phases.pdf

// TODO: simpoint http://cseweb.ucsd.edu/~calder/simpoint/

// TODO: nella scelta della base usare tecniche simili a PCA per analizzare la covarianza tra programmi e scegliere i programmi che sono poco ortogonali: 
// se P1 varia su dimensioni diversa da P2, non sono buoni predittori l' uno per l' altro! 
// PASSO 1: STUDIA LA MATEMATICA DIETRO PCA
// PASSO 2: misura distanza tra punti trasformati PCA e non trasformati, vedi se e' correlata con errore predizione
// PASSO 3: cerca o inventa una tecnica per scegliere punti che variano su dimensioni simili

// TODO: non linear regression http://www.eng.auburn.edu/~clemept/CEANALYSIS_FALL2011/Week1/non_Linearregression_paper.pdf


let printBatchOfRMSE3Asynch (basisT:basisType) samplesize =
    new Thread(fun () -> 
            let sb = new System.Text.StringBuilder()
            let conestring = basisTypeToString basisT
            let modelSizes = Array.init (10) (fun i -> 10 + i*20)
            let basisSizes = Array.init (14) (fun i -> 1 + 2*i)
            let pcNumbers = Array.init 10 (fun i -> 5 + i*5)
            let filename = System.String.Format("{0}RMSE_{1}_All_summary_sampleSize{2}.dat", folder, conestring, samplesize)
            modelSizes |> Array.iter (fun size -> 
                    basisSizes |> Array.iter (fun basis ->
                        pcNumbers |> Array.iter (fun pc ->
                            if (!stop) then raise (Exception("ABORT"))
                            //printf "model %i basis %i\n" size basis
                            //let average_average, average_stddev, RMSE_average, RMSE_stddev = 0.0, 0.0, 0.0, 0.0
                            estimatedComputationalPatterns := pc
                            let average_average, average_stddev, RMSE, errors = iterate basisT samplesize size basis
                            sb.AppendLine(System.String.Format("{0} {1} {2} {3} {4} {5}", pc, size, basis, average_average, average_stddev, RMSE)) |> ignore
                            // feedback to console
                            System.Console.WriteLine(System.String.Format("{0} {1} {2} {3} {4} {5} {6}", conestring, pc, size, basis, average_average, average_stddev, RMSE)) 
                        )
                    )
                )
            //System.Console.WriteLine(sb.ToString())
            System.IO.File.WriteAllText(filename, sb.ToString())
            System.Console.WriteLine("RMSE file written, all done")
        )


printf "\n--- fatto ----\n" 
    
// run a bunch of 'em
let runBunch cone size basisSize = Array.init 10 (id) |> Array.map (fun _ -> 
        //let avges, _, _, _, _, _, _, _ = runTest cone size basisSize
        let avges, res, basis, values_model, values_test, n, p = runTest false cone size basisSize
        let a,d,s = avges
        GC.WaitForFullGCComplete() |> ignore
        a,d, size, basisSize
        ) 


let printRMSE (basisT:basisType) (modelsize:int) (res:(float*float*int*int)[]) =
    let sb = new System.Text.StringBuilder()
    res |> Array.iter (fun (a,d,s,i) -> sb.AppendLine(System.String.Format("{0} {1} {2} {3}", s, i, a, d)) |> ignore)
    let conestring = basisTypeToString basisT
    let filename = System.String.Format("{0}RMSE_{1}_{2}.dat", folder, conestring, modelsize)
    System.IO.File.WriteAllText(filename, sb.ToString())

let printAllRMSE (basisT:basisType) modelsize (sizes:int[]) (res:(float*float*int*int)[][]) =
    Array.iter2 (fun size res -> printRMSE basisT size res) sizes res
    let sb = new System.Text.StringBuilder()
    let calcAvg (i:int) (res:(float*float*int*int)[]) =
        let avg = Array.average (res |> Array.map (fun (a,_,_,_) -> a))
        let dev = Array.average (res |> Array.map (fun (_,d,_,_) -> d))
        sb.AppendLine(System.String.Format("{0} {1} {2}", i, avg, dev)) |> ignore
    Array.iter2 calcAvg sizes res
    let conestring = basisTypeToString basisT
    let filename = System.String.Format("{0}RMSE_{1}_{2}_summary.dat", folder, conestring, modelsize)
    System.IO.File.WriteAllText(filename, sb.ToString())

let printBatchOfRMSE (basisT:basisType) data =
    let sbAll = new System.Text.StringBuilder()
    let conestring = basisTypeToString basisT
    let doStuff ((modelsize:int), (sizes:int[]), (res:(float*float*int*int)[][])) =
        Array.iter2 (fun size res -> printRMSE basisT size res) sizes res
        let sb = new System.Text.StringBuilder()
        let calcAvg (i:int) (res:(float*float*int*int)[]) =
            let avg = Array.average (res |> Array.map (fun (a,_,_,_) -> a))
            let dev = Array.average (res |> Array.map (fun (_,d,_,_) -> d))
            sb.AppendLine(System.String.Format("{0} {1} {2}", i, avg, dev)) |> ignore
            sbAll.AppendLine(System.String.Format("{0} {1} {2} {3}", modelsize, i, avg, dev)) |> ignore
        Array.iter2 calcAvg sizes res
        let filename = System.String.Format("{0}RMSE_{1}_{2}_summary.dat", folder, conestring, modelsize)
        System.IO.File.WriteAllText(filename, sb.ToString())
    data |> Seq.iter (fun d -> doStuff d)
    let filename = System.String.Format("{0}RMSE_{1}_All_summary.dat", folder, conestring)
    System.IO.File.WriteAllText(filename, sbAll.ToString())


let modelsize = 100
// test all sizes
let howmany = Array.init 20 (fun i -> i + 3)
let resCone = howmany |> Array.map (runBunch basisType.cone 4)
let resNoCone = howmany |> Array.map (runBunch basisType.gauss modelsize)

//printAllRMSE true howmany resCone
printAllRMSE basisType.gauss modelsize howmany resNoCone

printAllRMSE basisType.cone modelsize howmany resCone

// 3D graph, changing modelsize and basisize
let allres = Seq.init 20 (fun i -> (i+1)*10) |> Seq.map (fun modelsize ->  modelsize, howmany, howmany |> Array.map (runBunch basisType.gauss modelsize))
printBatchOfRMSE basisType.gauss allres


// k-means or mesh semplification

// http://www.cs.uu.nl/research/techreps/repo/CS-2007/2007-038.pdf

// http://webdocs.cs.ualberta.ca/~anup/Courses/604_3DTV/Presentation_files/Polygon_Simplification/7.pdf







let r = new System.Random()

//let rand = MathNet.Numerics.Distributions.ContinuousUniform(0.0, 1.0)
//let A = DenseMatrix.CreateRandom(20,2, rand)
//let A = DenseMatrix.OfRows(3,2, [| [| 0.1; 0.15 |]; [| 0.3; 0.29 |]; [| 0.6; 0.62 |] |])
//let A = DenseMatrix.OfRows(10,2, [| [| 2.5; 2.4 |]; [| 0.5; 0.7 |];[| 2.2; 2.9 |];[| 1.9;2.2 |];[|3.1;3.0 |];[|2.3;2.7 |];[| 2.0;1.6|];[| 1.0; 1.1 |];[| 1.5;1.6 |];[| 1.1; 0.9|]; |])

//let principalComponets = 2

let PCA (A:DenseMatrix) principalComponets =
    // subtract the mean of each column to each column
    let A1 = DenseMatrix.OfColumnVectors(Array.init (A.ColumnCount) (fun i -> 
                                        let c = A.Column(i) 
                                        c.Subtract(c.Mean()).Divide(c.StandardDeviation())
                                    ))
    // covariance matrix
    let covMatrix = DenseMatrix.Create(A1.ColumnCount, A1.ColumnCount, fun i j -> MathNet.Numerics.Statistics.ArrayStatistics.Covariance(A1.Column(i).AsEnumerable() |> Seq.toArray, A1.Column(j).AsEnumerable() |> Seq.toArray))
    // eigen values and vector of the covariance matrix
    let fact = covMatrix.Evd()
    let eigenValues = fact.EigenValues()
    let eigenVectors = fact.EigenVectors()
    let orderedEigenValues = eigenValues.AsEnumerable() |> Seq.mapi (fun i v -> i, v.Magnitude) |> Seq.sortBy snd |> Seq.skip (eigenValues.Count - principalComponets)
    let totenergy = eigenValues.AsEnumerable() |> Seq.map (fun v -> v.Magnitude) |> Seq.sum
    let energy = orderedEigenValues |> Seq.map snd |> Seq.sum
    let rowFeatureVector = DenseMatrix.OfRowVectors( orderedEigenValues |> Seq.map fst |> Seq.map (fun i -> eigenVectors.Column(i)) |> Seq.toArray |> Array.rev)
    let A1T = A1.Transpose()
    let finalData = rowFeatureVector.Multiply(A1T).Transpose()
    finalData, eigenValues, eigenVectors, energy/totenergy

//let data, eval, evect, info = PCA A 2

//let A = DenseMatrix.OfRows(8,2,[| [| 1.0;1.0 |]; [| 0.9;1.1 |]; [| 2.0;2.0 |];  [| 1.9;1.9 |]; [| 2.1;2.0 |]; [| 0.0;1.0 |]; [| 0.1;1.1 |]; [| 0.0;1.1 |]; |])



// k-means
let kmean (A:DenseMatrix) nCentroids =
    let distance (a:float seq) (b:float seq) =
        Seq.zip a b |> Seq.map (fun (v1,v2) -> v1-v2) |> Seq.map (fun v -> v*v) |> Seq.sum |> sqrt
    let points = Array.init (A.RowCount) (fun i -> A.Row(i).AsEnumerable() |> Seq.toArray)
    let samePoint (a: float seq) (b:float seq) =
        Seq.forall2 (fun e1 e2 -> e1=e2) a b 
    let makeAttempt () =
        // take nCentroids random points
        let initCentroids = points |> Array.map (fun p -> p, r.Next()) |> Array.sortBy snd |> Seq.take nCentroids |> Seq.map fst |> Seq.toArray
        let rec kmeanStep centroids iter =
            let findCluster centroids p =
                centroids |> Array.map (fun c -> c, distance c p)|> Array.sortBy snd |> Seq.head
            let clusters = points |> Array.map (fun p -> p, findCluster centroids p)
            let moveCentroid c =
                let myPoints = clusters |> Array.filter (fun (p,(c1,d)) -> c=c1 )
                if (myPoints.Length > 0) then
                    let thisCluster = myPoints |> Array.map fst
                    Array.init (thisCluster.[0] |> Seq.length ) (fun i -> thisCluster |> Array.map (fun v -> Seq.nth i v) |> Array.average )
                else
                    // this cluster is empty! move to the point with higher distance
                    clusters |> Array.sortBy (fun (p,(c,d)) -> d) |> Array.rev |> Seq.head |> fst
            let newCentroids = centroids |> Array.map moveCentroid
            let hasPoint p =
                centroids |> Array.exists (fun p2 -> samePoint p p2)
            let allSame = newCentroids |> Array.forall hasPoint
            if (allSame || iter = 0) then
                let cost = points |> Array.map (fun p -> p, findCluster newCentroids p) |> Array.map snd |> Array.map snd |> Array.average
                newCentroids, cost
            else
                kmeanStep newCentroids (iter-1)
        let centroids, cost = kmeanStep initCentroids 100
        let findBest c =
            points |> Array.map (fun p -> p, distance p c) |> Array.sortBy snd |> Array.map fst |> Seq.head
        centroids |> Array.map (fun c -> findBest c), cost

    let finalCentroids, cost = Array.init 10 (fun i -> makeAttempt()) |> Array.sortBy snd  |> Seq.head
    let findIndex c =
        points |> Array.mapi (fun i p -> i, samePoint c p) |> Array.filter (fun (i,b) -> b) |> Array.map fst |> Seq.head
    finalCentroids |> Array.map findIndex, finalCentroids, cost



//let basis, centroids, cost = kmean (DenseMatrix.OfMatrix(data)) 3

    
#I @"C:\Users\davidemorelli\AppData\Roaming\Local Libraries\Local Documents\GitHub\Energon\Charts"
#r "MSDN.FSharpChart.dll"
open MSDN.FSharp.Charting

//Array.init (A.RowCount) (fun i -> A.Row(i).AsEnumerable() |> Seq.toArray) |> Array.map (fun p -> p.[0], p.[1]) |> FSharpChart.Point |> FSharpChart.Create
//Array.init (data.RowCount) (fun i -> data.Row(i).AsEnumerable() |> Seq.toArray) |> Array.map (fun p -> p.[0], p.[1]) |> FSharpChart.Point |> FSharpChart.Create
//centroids |> Array.map (fun p -> p.[0], p.[1]) |> FSharpChart.Point |> FSharpChart.Create


// -------------------- complete refactor -------------------- 

// extracts modelSize and testSize rows from M randomly and returns the model and test matrices
let extractModel (M:DenseMatrix) modelSize testSize =
    let r = new System.Random()
    let indices = Seq.init (M.RowCount) (fun i -> i,r.NextDouble()) |> Seq.sortBy (fun (i,v) -> v) |> Seq.map fst |> Seq.take (modelSize + testSize)
    let indicesModel = indices |> Seq.take modelSize
    let indicesTest = indices |> Seq.skip modelSize
    let matrixModel = DenseMatrix.OfRowVectors(indicesModel |> Seq.map (fun i -> M.Row(i)) |> Seq.toArray)
    let matrixTest = DenseMatrix.OfRowVectors(indicesTest |> Seq.map (fun i -> M.Row(i)) |> Seq.toArray)
    matrixModel, matrixTest

// find the best basis out of the M matrix, and returns:
// the indices of the basis
// the names of the programs in the basis
// the estimated basis quality (0 means good)
let findBasis (basisT:basisType) (M:DenseMatrix) basisSize =
    let data, eval, evect, info = PCA (DenseMatrix.OfMatrix(M.Transpose())) 4
    //System.Console.WriteLine("data: {0}", data.ToString(100,100))
    //System.Console.WriteLine("info: {0}", info)
    
    //let data, eval, evect, info = PCA (DenseMatrix.OfMatrix(M.Transpose())) 4
    let basisIndices, centroids, cost = kmean (DenseMatrix.OfMatrix(data)) basisSize

    //System.Console.WriteLine("basisIndices: ")
    //basisIndices |> Array.iter (fun i-> System.Console.Write(" {0}", i))
    //System.Console.WriteLine("")
    //System.Console.WriteLine("cost: {0}", cost)
    
    //let dataToPlot = Array.init (data.RowCount) (fun i -> data.Row(i)) |> Array.map (fun p -> p.[0],p.[1])
    //let centroidsToPlot = centroids |> Array.map (fun c -> c.[0],c.[1])
    //[| dataToPlot |> FSharpChart.Point :> ChartTypes.GenericChart ; centroidsToPlot |> FSharpChart.Point :> ChartTypes.GenericChart |] |> FSharpChart.Combine |> FSharpChart.Create |> ignore
    let basisNames = [| " " |]
    basisIndices, basisNames, cost, info

let OLS (A:DenseMatrix) (b:DenseVector) =
    if (A.RowCount < A.ColumnCount) then
        // A is underdetermined
        // using http://see.stanford.edu/materials/lsoeldsee263/08-min-norm.pdf
        if (A.Rank() < A.RowCount) then 
            failwith "A is not full rank, cannot invert"
        A.Transpose().Multiply((A.Multiply(A.Transpose())).Inverse()).Multiply(b)
    else
        // A is not underdetermined
        A.QR().Solve(b)

let NMF (v:DenseMatrix) pc =
    let costF (A:DenseMatrix) (B:DenseMatrix) =
        let C = A.Subtract(B)
        seq {
            for i in 0..(C.RowCount-1) do
                for j in 0..(C.ColumnCount-1) do
                    yield C.Item(i,j)
            } |> Seq.map (fun v -> v*v) |> Seq.sum
    let r = new ContinuousUniform(0.0, 1.0)
    let ic = v.RowCount    
    let fc = v.ColumnCount
    let w = DenseMatrix.CreateRandom(ic, pc, r)
    let h = DenseMatrix.CreateRandom(pc, fc, r)
    let epsilon = 0.000001
    let rec factorize (v:DenseMatrix) (h:DenseMatrix) (w:DenseMatrix) iter =
        let wh = w.Multiply(h)
        let cost = costF v (DenseMatrix.OfMatrix(wh))
        if (cost<epsilon || iter = 0) then
            h,w
        else
            let hn = w.Transpose().Multiply(v)
            let hd = w.Transpose().Multiply(w).Multiply(h)
            let h_cols = h.ToColumnWiseArray()
            let hn_cols = hn.ToColumnWiseArray()
            let hd_cols = hd.ToColumnWiseArray()
            let newh_cols = Array.mapi (fun i v -> v*hn_cols.[i]/hd_cols.[i]) h_cols
            let newh = DenseMatrix.OfColumnMajor(h.RowCount, h.ColumnCount, newh_cols )
            let wn = v.Multiply(newh.Transpose())
            let wd = w.Multiply(newh.Multiply(newh.Transpose()))
            let w_cols = w.ToColumnWiseArray()
            let wn_cols = wn.ToColumnWiseArray()
            let wd_cols = wd.ToColumnWiseArray()
            let neww_cols = Array.mapi (fun i v -> v*wn_cols.[i]/wd_cols.[i]) w_cols
            let neww = DenseMatrix.OfColumnMajor(w.RowCount, w.ColumnCount, neww_cols )
            factorize v newh neww (iter-1)
    let h,w = factorize v h w 50
    let cost = costF v (DenseMatrix.OfMatrix(w.Multiply(h)))
    h,w,cost

//let a  =DenseMatrix.CreateRandom(1,3,new MathNet.Numerics.Distributions.ContinuousUniform())
//let h,w,c= NMF a 1
//let A = DenseMatrix.OfMatrix(H.Transpose())
//let b = a

let NNLS (A:DenseMatrix) (b:DenseVector) =
    // see http://books.google.it/books?hl=en&lr=&id=LU5_2sWlVlMC&oi=fnd&pg=PP2&ots=x2kEt5s5kG&sig=HbeDhVWlooj91jYrD8pR9k5mzLk&redir_esc=y#v=onepage&q&f=false
    // pag 161
    let n = A.ColumnCount
    // step 1
    let P = []
    let Z = [0..(n-1)]
    // let x = (DenseVector.zeroCreate(n))
    // let z = (DenseVector.zeroCreate(n))
    let checkIter iter =
        if (iter < 0) then
            System.Console.WriteLine("infinite loop detected!")
            System.Console.WriteLine(A.ToMatrixString(A.RowCount, A.ColumnCount))
            System.Console.WriteLine(b.ToVectorString(300,300))
            raise (Exception("infinite loop"))
    let steps2to5 (x:DenseVector) (z:DenseVector) (P:int list) (Z:int list) f iter =
        checkIter iter
        // step 2
        let w = A.Transpose().Multiply(b - A.Multiply(x))
        // step 3
        if (Z.IsEmpty || Z |> List.map (fun j -> w.Item(j) <= 0.0) |> List.forall (id)) then
            //System.Console.WriteLine("solved in " + iter.ToString() + " steps" )
            x
        else
            // step 4
            let t,max = Z |> List.map (fun j -> j, w.Item(j)) |> List.maxBy (fun (j,v) -> v)
            // step 5
            let P2 = t::P
            let Z2 = Z |> List.filter (fun j -> j <> t)
            // let P = P2
            // let Z = Z2
            f x z P2 Z2 (iter-1)
    let rec steps6to11 (x:DenseVector) (z:DenseVector) (P:int list) (Z:int list) iter =
        checkIter iter
        // step 6
        let Ap = DenseMatrix.ofColumnVectors( List.init (A.ColumnCount) (fun j -> if  P.Contains(j) then A.Column(j) else DenseVector.zeroCreate(A.RowCount) :> LinearAlgebra.Generic.Vector<float> ))
        let btmp = DenseVector.ofSeq( List.init (b.Count) (fun j -> if P.Contains(j) then b.[j] else 0.0))
        let zp = OLS Ap btmp
        let z = DenseVector.zeroCreate(n)
        P |> List.iter (fun v -> z.Item(v) <- zp.Item(v) )
        // step 7
        if (P |> List.map (fun j -> z.Item(j) > 0.0) |> List.forall (id)) then
            //printf "go to step 2\n"
            // iterate
            steps2to5 z z P Z steps6to11 (iter - 1)
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
            steps6to11 (DenseVector.OfVector(x)) (DenseVector.OfVector(z)) P2 Z2 (iter - 1)

    steps2to5 (DenseVector.zeroCreate(n)) (DenseVector.zeroCreate(n)) P Z steps6to11 10000


let findPredictors (basisT:basisType) (A:DenseMatrix) (b:DenseVector) =
    let getRow (measures:float[][]) i =
        measures |> Array.map (fun r -> r.[i])
    let filterRows (measures:float[][]) (indices:int[]) =
        let filterRow (r:float[]) =
            r |> Array.mapi (fun i v -> i,v) |> Array.filter (fun (i,v) -> indices.Contains(i)) |> Array.map snd
        measures |> Array.map filterRow



    // performs a prediction and returns it with the confidence
    let predict (aTest:DenseVector) =
        match basisT with
        | basisType.NNLS ->
            let splitup = NNLS A b
            let prediction = Seq.map2 (*) (aTest) (splitup) |> Seq.sum
            prediction, 0.0
        | basisType.NNMF ->

            let predictNMF (H:DenseMatrix) (W:DenseMatrix) (b:DenseVector) (a:DenseVector) =
                //let w = H.Transpose().Svd(true).Solve(a)
                let w = NNLS (DenseMatrix.OfMatrix(H.Transpose())) a
                //let h = W.Svd(true).Solve(b)
                let h = NNLS W b
                let prev = h.ToRowMatrix().Multiply(w)
                prev.Item(0)
            let H,W,c = NMF A (!estimatedComputationalPatterns)
            let predicted = predictNMF H W b aTest
            predicted, c
        | basisType.cone ->
            (*
            let s = new SplitupFinder()
            let programs = Array.init (basis.Length) (id) |> Array.map (getRow testbed_model) |> Array.map (fun r -> 
                    let p = new Program()
                    p.Measures <- r
                    p
                )
            s.Testbed <- programs
            let handleProg (i:int) =
                let model = getRow programs_model i
                let test = getRow programs_test i
                let name = programNames.[programsIndices.[i]]
                let idx = programsIndices.[i]
                let p = new Program()
                p.Measures <- model
                s.Target <- p
                if (s.FindSplitup(true)) then
                    let splitup = s.Splitup
                    let a,d, e, s = programErrors test testbed_test splitup
                    idx, name, a, d, e, s
                else
                    System.Console.WriteLine("could not find a splitup for program {0} {1}", i, name)
                    idx, name, 0.0, 0.0, [| |], [| |]
            // pick a program of the availables and test
            let res = handleProg 0
            [| res |]
            *)
            0.0, 0.0
        | basisType.gauss ->
            let splitup = OLS A b
            let confidence = A.Multiply(DenseVector.ofSeq(splitup)).Subtract(b).Norm(2.0)
            //System.Console.WriteLine("splitup is")
            //splitup |> Array.iter (fun v -> System.Console.Write(" {0}", v))
            //System.Console.WriteLine("")
            let prediction = Seq.map2 (*) (aTest) (splitup) |> Seq.sum
            prediction, confidence
        | basisType.tls ->
            let TotalLeastSquare (X:DenseMatrix) (y:DenseVector) =
                let m = X.RowCount
                let n = X.ColumnCount
                let Xmat = X
                let Ymat = y
                let Zmat = Xmat.Append(Ymat.ToColumnMatrix())
                let svd = Zmat.Svd(true)
                let Smat = svd.S()
                let Umat = svd.U()
                let VTmat = svd.VT()
                let Vmat = VTmat.Transpose()
                let VXY = Vmat.SubMatrix(0, n, n, (Vmat.ColumnCount - n))
                let VYY = Vmat.SubMatrix(n, (Vmat.RowCount - n), n, (Vmat.ColumnCount - n))
                let B = (-VXY).Divide(VYY.At(0,0))
                B.Column(0).ToArray()
            let splitup = TotalLeastSquare A b
            let prediction = Seq.map2 (*) (aTest) (splitup) |> Seq.sum
            prediction, 0.0
    predict

// execute one full experiment
// returns the average error, errors standard deviations, RMSE and the list of all the errors (to compute the overall rmse)
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
    let testbedModel = DenseMatrix.OfColumnVectors( Seq.init (matrixModelNoTarget.ColumnCount) (id) |> Seq.filter (fun i -> basisIndices.Contains(i) ) |> Seq.map (fun i -> matrixModelNoTarget.Column(i)) |> Seq.toArray)
    let testbedTest = DenseMatrix.OfColumnVectors( Seq.init (matrixTestNoTarget.ColumnCount) (id) |> Seq.filter (fun i -> basisIndices.Contains(i) ) |> Seq.map (fun i -> matrixTestNoTarget.Column(i)) |> Seq.toArray)
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
let runSeveralExperiments (M:DenseMatrix) (basisT:basisType) modelSize testSize basisSize iter targetProgram =
    let predictions = Seq.init iter (fun  _ -> runOneExperiment M basisT modelSize testSize basisSize targetProgram)
    let averages = predictions |> Seq.map (fun (average, stdDev, rmse, errors) -> average)
    let stdDev = predictions |> Seq.map (fun (average, stdDev, rmse, errors) -> stdDev)
    let rmse = predictions |> Seq.map (fun (average, stdDev, rmse, errors) -> rmse)
    let errors = predictions |> Seq.map (fun (average, stdDev, rmse, errors) -> errors) |> Seq.concat
    let errorsRmse = errors |> Seq.map (fun v -> v*v) |> Seq.average |> sqrt
    averages.Mean(), averages.StandardDeviation(), stdDev.Mean(), stdDev.StandardDeviation(), rmse.Mean(), rmse.StandardDeviation(), errors.Mean(), errors.StandardDeviation(), errorsRmse, errors

let runExperimentsAllPrograms  (M:DenseMatrix)  (basisT:basisType) modelSize testSize basisSize iter =
    let predictions = Seq.init (values_array.[0].Length) (fun i -> i, runSeveralExperiments M basisT modelSize testSize basisSize iter i)
    predictions

open System.Threading

// transform measures into a Dense Matrix
let valuesSequence = Seq.init (values_array.Length) (fun i -> values_array.[i] |> Array.toSeq)
let M = DenseMatrix.OfMatrix(DenseMatrix.OfRows(values_array.Length, values_array.[0].Length, valuesSequence).NormalizeRows(1))

runSeveralExperiments M (basisType.gauss) 50 50 20 10 1

let predictions = runExperimentsAllPrograms M (basisType.gauss) 50 1 20 30 |> Seq.toArray
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
    let n = r.Next(16)+1
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

runSeveralExperiments N (basisType.NNMF) 2 1 1 10 1

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


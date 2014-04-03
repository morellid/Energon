module Solvers
//namespace Solvers

open MathNet.Numerics.LinearAlgebra.Double
open MathNet.Numerics.Distributions
open System
open System.Collections.Generic

let r = new System.Random()

module helpers =
    let predict f (A:DenseMatrix) (b:DenseVector) (a:DenseVector) =
        let x:DenseVector = f A b
        let err = A.Multiply(DenseVector.ofSeq(x)).Subtract(b).Norm(2.0) 
        let prediction = x.ToColumnMatrix().Multiply( a.ToRowMatrix() ).Item(0,0)
        prediction, err
/// Principal Component Analysis of a DenseMatrix A using principalComponents hidden features.
/// Returns the initial data projected on the components, the eigen values, the eigen vectors, the ratio beteen the energy contained in the projetion and the total energy
let PCA (A:DenseMatrix) principalComponets =
    // subtract the mean of each column to each column
    let A1 = DenseMatrix.OfColumnVectors(Array.init (A.ColumnCount) (fun i -> 
                                        let c = A.Column(i) 
                                        let m = c.ToArray() |> Array.average
                                        let sd = c.ToArray() |> Seq.map (fun v -> v-m) |> Seq.map (fun v -> v*v) |> Seq.average
                                        c.Subtract(m).Divide(sd)
                                    ))
    // covariance matrix
    let covMatrix = DenseMatrix.Create(A1.ColumnCount, A1.ColumnCount, fun i j -> MathNet.Numerics.Statistics.ArrayStatistics.Covariance(A1.Column(i).ToArray() |> Seq.toArray, A1.Column(j).ToArray() |> Seq.toArray))
    // eigen values and vector of the covariance matrix
    let fact = covMatrix.Evd()
    let eigenValues = fact.EigenValues()
    let eigenVectors = fact.EigenVectors()
    let orderedEigenValues = eigenValues.ToArray() |> Seq.mapi (fun i v -> i, v.Magnitude) |> Seq.sortBy snd |> Seq.skip (eigenValues.Count - principalComponets)
    let totenergy = eigenValues.ToArray() |> Seq.map (fun v -> v.Magnitude) |> Seq.sum
    let energy = orderedEigenValues |> Seq.map snd |> Seq.sum
    let rowFeatureVector = DenseMatrix.OfRowVectors( orderedEigenValues |> Seq.map fst |> Seq.map (fun i -> eigenVectors.Column(i)) |> Seq.toArray |> Array.rev)
    let A1T = A1.Transpose()
    let finalData = rowFeatureVector.Multiply(A1T).Transpose()
    finalData, eigenValues, eigenVectors, energy/totenergy



/// k-means clustering algorithm. Every row of the A matrix is a point, we cluster into nCentroids clusters. NB: points are the rows, not the columns of A
let kmean (A:DenseMatrix) nCentroids =
    let distance (a:float seq) (b:float seq) =
        Seq.zip a b |> Seq.map (fun (v1,v2) -> v1-v2) |> Seq.map (fun v -> v*v) |> Seq.sum |> sqrt
    let points = Array.init (A.RowCount) (fun i -> A.Row(i).ToArray() |> Seq.toArray)
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

/// Ordinary Least Squares Linear solver, finds x such as Ax=b
let OrdinaryLeastSquares (A:DenseMatrix) (b:DenseVector) =
    if (A.RowCount < A.ColumnCount) then
        // A is underdetermined
        // using http://see.stanford.edu/materials/lsoeldsee263/08-min-norm.pdf
        if (A.Rank() < A.RowCount) then 
            failwith "A is not full rank, cannot invert"
        DenseVector.OfVector(A.Transpose().Multiply((A.Multiply(A.Transpose())).Inverse()).Multiply(b))
    else
        // A is not underdetermined
        DenseVector.OfVector( A.QR().Solve(b))


/// Non Negative Least Squares Linear solver, finds x such as Ax=b, with the constraint that x is positive
let NonNegativeLeastSquares (A:DenseMatrix) (b:DenseVector) =
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
        let Ap = DenseMatrix.ofColumnVectors( List.init (A.ColumnCount) (fun j -> if ( P |> List.exists ((=) j)) then A.Column(j) else DenseVector.zeroCreate(A.RowCount) :> _ ))
        let btmp = DenseVector.ofSeq( List.init (b.Count) (fun j -> if ( P |> List.exists ((=) j)) then b.[j] else 0.0))
        let zp = OrdinaryLeastSquares Ap btmp
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
            let P2 = P |> List.filter (fun j -> not( commuters |> List.exists ((=) j) ))
            // go to step 6
            steps6to11 (DenseVector.OfVector(x)) (DenseVector.OfVector(z)) P2 Z2 (iter - 1)

    steps2to5 (DenseVector.zeroCreate(n)) (DenseVector.zeroCreate(n)) P Z steps6to11 10000

/// Total Least Squares Linear solver.
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
    DenseVector.OfEnumerable (B.Column(0).ToArray())

(*
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
*)

/// Non Negative Matrix Factorization: finds the matrices H and W such as HW=A. H has pc rows and W has pc columns, pc is the number of hidden features.
/// Returns H, W and the difference between A and HW, squared, summing all the elements.
let NonNegativeMatrixFactorization (v:DenseMatrix) pc =
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


let predictUsingTotalLeastSquares A b (a:DenseVector) =
    helpers.predict TotalLeastSquare A b a

let predictUsingNonNegativeLeastSquares A b (a:DenseVector) =
    helpers.predict NonNegativeLeastSquares A b a

let predictUsingOrdinaryLeastSquares A b (a:DenseVector) =
    helpers.predict OrdinaryLeastSquares A b a

let predictUsingNonNegativeMatrixFactorization A b (a:DenseVector) (components) =
    let H,W,cost = NonNegativeMatrixFactorization A components
    let w = NonNegativeLeastSquares (DenseMatrix.OfMatrix(H.Transpose())) a
    let h = NonNegativeLeastSquares W b
    let prev = h.ToRowMatrix().Multiply(w)
    prev.Item(0), cost


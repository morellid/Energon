﻿#I @"C:\Users\davide\Documents\GitHub\Energon\bin\Debug"
#r @"Energon.Measuring.dll"
open Energon.Measuring

#r @"Energon.Storage.dll"
//#r @"C:\Users\Davide\Desktop\Projects\Energon\Storage\bin\Debug\Energon.Measurement.dll"
//#r @"C:\Users\Davide\Desktop\Projects\Energon\SqlCompactDb\Measurement\bin\Debug\Energon.Measurement.dll"

#r "SQLExpress.dll"
#r "System.Data.Linq.dll"
#r "System.Linq.dll"
#r "FSharp.PowerPack.Linq.dll"
#r "System.Data.DataSetExtensions.dll"
#r "System.Core.dll"

open System
open System.Data.Linq.SqlClient
open System.Linq
open Microsoft.FSharp.Linq
open System.Data.Linq
open Energon.Measuring
open System.Text
//open System.Data.DataSetExtensions
let dbfile = @"C:\Users\root\Desktop\Energon\Measurements.sdf"


#r @"Energon.Phidgets.dll"
open Phidgets30A

openPhidgets() 

let phidgetAmmeter = new AmmeterSensor("PhidgetsVA", 0, ifkit, 10.)

//let sensors = [| extechWatt :> GenericSensor ; new RemoteSensor("test", DataType.Unknown) :> GenericSensor; new RemoteSensor("test", DataType.Unknown) :> GenericSensor|]
//let sensors = [| new RemoteSensor("cpu-cycles", DataType.Unknown) :> GenericSensor; new RemoteSensor("cache-references", DataType.Unknown) :> GenericSensor; new RemoteSensor("cache-misses", DataType.Unknown) :> GenericSensor; new RemoteSensor("branch-instructions", DataType.Unknown) :> GenericSensor; new RemoteSensor("branch-misses", DataType.Unknown) :> GenericSensor; new RemoteSensor("seconds", DataType.Unknown) :> GenericSensor|]
//let sensors = [| extechWatt :> GenericSensor; new RemoteSensor("cpu-cycles", DataType.Unknown) :> GenericSensor; new RemoteSensor("cache-references", DataType.Unknown) :> GenericSensor; new RemoteSensor("cache-misses", DataType.Unknown) :> GenericSensor; new RemoteSensor("branch-instructions", DataType.Unknown) :> GenericSensor; new RemoteSensor("branch-misses", DataType.Unknown) :> GenericSensor; new RemoteSensor("seconds", DataType.Unknown) :> GenericSensor|]
let sensors = [| phidgetAmmeter :> GenericSensor; new RemoteSensor("cpu-cycles", DataType.Unknown) :> GenericSensor; new RemoteSensor("cache-references", DataType.Unknown) :> GenericSensor; new RemoteSensor("cache-misses", DataType.Unknown) :> GenericSensor; new RemoteSensor("branch-instructions", DataType.Unknown) :> GenericSensor; new RemoteSensor("branch-misses", DataType.Unknown) :> GenericSensor; new RemoteSensor("seconds", DataType.Unknown) :> GenericSensor|]
let sensors = [| new RemoteSensor("cpu-cycles", DataType.Unknown) :> GenericSensor; 
                new RemoteSensor("cache-references", DataType.Unknown) :> GenericSensor; 
                new RemoteSensor("cache-misses", DataType.Unknown) :> GenericSensor; 
                new RemoteSensor("branch-instructions", DataType.Unknown) :> GenericSensor; 
                new RemoteSensor("branch-misses", DataType.Unknown) :> GenericSensor; 
                new RemoteSensor("seconds", DataType.Unknown) :> GenericSensor|]

let sensors = [| phidgetAmmeter :> GenericSensor; new RemoteSensor("faults", DataType.Unknown) :> GenericSensor; new RemoteSensor("seconds", DataType.Unknown) :> GenericSensor|]

let sensors = [| new RemoteSensor("faults", DataType.Unknown) :> GenericSensor; new RemoteSensor("seconds", DataType.Unknown) :> GenericSensor|]

let sensors = [| new RemoteSensor("Perc Proc User Time", DataType.Unknown) :> GenericSensor; new RemoteSensor("Page Faults per sec", DataType.Unknown) :> GenericSensor; new RemoteSensor("seconds", DataType.Unknown) :> GenericSensor|]

// declare a remote sensor

//let sensors = [|extechAmp :> GenericSensor; extechWatt :> GenericSensor; extechPF :> GenericSensor; extechV :> GenericSensor; r1 :> GenericSensor |]
//let sensors = [| r1 :> GenericSensor |]


// DEBUG
open Energon.Measuring.Remote

// iozone
let e = new Experiment("iozone_ubuntu32kvm_load4", sensors, 0, [| "prog"; "size" |], [||], fun _ -> ())

let system = "sl64kvm_256RAM_loadHeap16"
let system = "ATOM_OptiPlex"
let system = "Vostro_Ubuntu64"
let system = "armv71_tegra"
let system = "Vostro_win7"

// db helper
//let server = "HPLAB\SQLEXPRESS"
let server = "MANDARINO\MISURATORE"
let dbname = "Measures"

let createExp (prog:string) (system:string) =
  new Experiment(System.String.Format("{0}_{1}", prog, system), sensors, 0, [| "size" |], [||], fun _ -> ())

let createAndStartExp prog sys =
  let e = createExp prog sys
  let saver = new Energon.Storage.ExperimentRuntimeSaverExpress(e, server, dbname )
  new RemoteExperimentHelper(e, "0")


let e = createAndStartExp "quick" system
e.Start ()
e.Stop()

let e = createAndStartExp "merges" system
e.Start()
e.Stop()

let e = createAndStartExp "randMemAccess" system
e.Start()
e.Stop()

let e = createAndStartExp "simpleINT" system
e.Start()
e.Stop()

let e = createAndStartExp "simpleFPU" system
e.Start()
e.Stop()

let e = createAndStartExp "pi" system
e.Start()
e.Stop()

let e = createAndStartExp "heap" system
e.Start()
e.Stop()

let e = createAndStartExp "bubble" system
e.Start()
e.Stop()


//let e = new Experiment("test_linux", sensors, 0, [| "size" |], [||], fun _ -> ())


e.Start()
e.Stop()

// --------------------- ANALYSE ------------------

#r @"Energon.Measuring.dll"
#r @"Energon.Storage.dll"
#r "System.Data.Linq.dll"
#r "System.Linq.dll"

#r "FSharp.PowerPack.Linq.dll"
//#r "FSharp.Data.TypeProviders.dll"

#r "System.Data.DataSetExtensions.dll"
#r "System.Core.dll"
#r "SQLExpress.dll"

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
open SQLExpress

type HandySensor () as self =
    let mutable sensorID = 0
    let mutable sensorName = ""
    let mutable measurements:seq<float> = Seq.empty<float>
    let mutable average = 0.
    let mutable stddev = 0.
    member x.SensorID 
        with get() = sensorID
        and set(v) = sensorID <- v
    member x.SensoName
        with get() = sensorName
        and set(v) = sensorName <- v
    member x.Measurements 
        with get() = measurements
        and set(v) = measurements <- v
    member x.Average
        with get() = average
        and set(v) = average <- v
    member x.StandardDeviation
        with get() = stddev
        and set(v) = stddev <- v

let server = "MANDARINO\MISURATORE"
let database = "Measures"

let getConStr = 
        //let conStr = System.String.Format("server='{0}';database='{1}';User Id='{2}';password='{3}';", server, database, user, password) in
        let conStr = System.String.Format("Data Source={0};Initial Catalog={1};Integrated Security=SSPI;", server, database) in
                conStr
let GetLinqContext = 
        let context = new SQLExpress.Measure(getConStr)
        if (context.DatabaseExists() = false) then
             context.CreateDatabase()
        context
let db = 
        let context = GetLinqContext
        context.Connection.Open()
        context
        
let exp ids = Seq.collect (fun (i:int) -> db.Experiments.Where(fun (e:Experiments) -> e.Id = i)) ids
let cases exp = Seq.collect (fun (e:Experiments) -> db.ExperimentCases.Where(fun (c:ExperimentCases) -> c.Experiment_id = e.Id) ) exp

let getAveragesForCase case =
    db.AvgMeasures.Where(fun (a:AvgMeasures) -> (a.Experiment_case_id = case)).OrderBy(fun x -> x.Sensor_class_id)

let ts = getAveragesForCase 3416
Seq.map (fun (a:AvgMeasures) -> System.Console.WriteLine("{0}", a.SensorName)) ts

let caseid = 3409

let averagePhi = 0.7
let WsensorID = 94
let V = 220.0

let otherWsensor = 22
//let averagePhi = 1.0
//let WsensorID = 22
//let V = 1.0

let caseToAverages caseid =
    let avgs = getAveragesForCase caseid
    let w = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id=WsensorID).First()
    let s = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id=87).First()
    let j = w.Average.Value * s.Average.Value * averagePhi * V
    let filtered = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id <> WsensorID)
    let response = Seq.map (fun (a:AvgMeasures) -> a.Average.Value) filtered
    Seq.append response [| j |]

let caseToAveragesOnlyJ caseid =
    let avgs = getAveragesForCase caseid
    let w = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id=WsensorID).First()
    let s = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id=87).First()
    let j = w.Average.Value * s.Average.Value * averagePhi * V
    j

let caseToAveragesOnlyT caseid =
    let avgs = getAveragesForCase caseid
    let s = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id=87).First()
    s.Average.Value

let caseToAveragesNoJ caseid =
    let avgs = getAveragesForCase caseid
    let filtered = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id <> WsensorID && a.Sensor_class_id <> otherWsensor)
    let response = Seq.map (fun (a:AvgMeasures) -> a.Average.Value) filtered
    response

let caseToAveragesNoJNoBranch caseid =
    let avgs = getAveragesForCase caseid
    //let filtered = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id <> WsensorID && a.Sensor_class_id <> otherWsensor)
    //let filtered = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id <> WsensorID && a.Sensor_class_id <> otherWsensor && a.Sensor_class_id <> 90 && a.Sensor_class_id <> 91 && a.Sensor_class_id <> 95 && && a.Sensor_class_id <> 88 )
    let filtered = avgs.Where(fun (a:AvgMeasures) -> a.Sensor_class_id <> WsensorID && a.Sensor_class_id <> otherWsensor && a.Sensor_class_id <> 90 && a.Sensor_class_id <> 91 && a.Sensor_class_id <> 95 && a.Sensor_class_id <> 88 && a.Sensor_class_id <> 86 )
    let response = Seq.map (fun (a:AvgMeasures) -> a.Average.Value) filtered
    response

let caseToAveragesFinal = caseToAveragesNoJNoBranch

// print sensornames
//let caseid = 3206
//Seq.iter (fun (c:AvgMeasures) -> System.Console.WriteLine("{0}:{1}:{2}",c.Sensor_class_id, c.SensorName, c.Average.Value)) ( getAveragesForCase caseid)

// print values
//Seq.iter (fun (c:float) -> System.Console.WriteLine("{0}", c)) (caseToAverages caseid)
//Seq.iter (fun (c:float) -> System.Console.WriteLine("{0}", c)) (caseToAveragesNoJ caseid)

#r "GlpkProxy.dll"
open GlpkProxy

let getProgAverages (list:seq<int>) =
    Seq.fold (fun (state:seq<float>) (id:int) -> Seq.append state (caseToAveragesFinal id)) Seq.empty<float> list
let getTestBedAverages (list:seq<int array>) =
    Seq.map (fun (l:int array) -> getProgAverages l) list    
let getTestBedAveragesArrays (list:seq<int array>) =
    (Seq.map (fun (l:int array) -> (getProgAverages l).ToArray() ) list).ToArray()   
let buildTestBed (list:seq<seq<float>>) =
    let programFromAverages (l:seq<float>) =
        let p = new Program()
        p.Measures <- l.ToArray()
        p
    let programSeq = Seq.map (fun (l:seq<float>) -> programFromAverages l) list
    programSeq.ToArray()

let getProgNames (list:seq<int>) =
    let concatNameAndArgs (name:string) (args:string) = 
        //String.Format("{0}_{1}", name, args)
        name
    let getExperimentNameAndArgs caseid = 
        let tmp = db.ExperimentAndCases.Where(fun (e:ExperimentAndCases) -> e.Id = caseid).First()
        concatNameAndArgs (tmp.Name) (tmp.Args)
    Seq.fold (fun (state:seq<string>) (id:int) -> Seq.append state [|getExperimentNameAndArgs id|]) Seq.empty<string> list

let getProgNamesAndArgs (list:seq<int>) =
    let concatNameAndArgs (name:string) (args:string) = 
        String.Format("{0}_{1}", name, args.Replace(";", "_"))
    let getExperimentNameAndArgs caseid = 
        let tmp = db.ExperimentAndCases.Where(fun (e:ExperimentAndCases) -> e.Id = caseid).First()
        concatNameAndArgs (tmp.Name) (tmp.Args)
    Seq.fold (fun (state:seq<string>) (id:int) -> Seq.append state [|getExperimentNameAndArgs id|]) Seq.empty<string> list

let getColumnsNames (list:seq<int array>) =
    getProgNamesAndArgs (Seq.map (fun (l:int array) -> l.[0]) list)

let sanityzeString (s:string) = 
    s.Replace(";", " ")

let sanityzeStringSeq (l:seq<string>) =
    Seq.map sanityzeString l

open System.Globalization


let getEstimationError (target:int) (casesTestbed:seq<int>) (splitup:seq<float>) =
    let testbedMeasuredT =  Seq.map (fun (id:int) -> caseToAveragesOnlyT id) casesTestbed
    let estimateT =
        let zipped = Seq.zip testbedMeasuredT splitup
        Seq.fold (fun (state:float) (a:float,b:float) -> state + a*b) 0.0 zipped
    let measuredTargetT = caseToAveragesOnlyT target
    let difference = Math.Abs(measuredTargetT - estimateT)
    let percentage = difference / measuredTargetT
    (measuredTargetT, estimateT, difference, percentage)

let printEstimationErrors (target:int) (casesTestbed:seq<int>) (splitup:seq<float>) (sb:StringBuilder) =
    let expandcase id = db.ExperimentAndCases.Where(fun (c:ExperimentAndCases) -> c.Id = id).First()
    let getname (expandcase:ExperimentAndCases) = 
        String.Format("{0}_{1}", expandcase.Name, expandcase.Args)
    let appendInfo id =
        let name = getname (expandcase id)
        let m,e,d, p = getEstimationError id casesTestbed splitup
        sb.AppendLine(String.Format("{0};{1};{2};{3};{4}", sanityzeString name, m, e, d, p)) |> ignore
    appendInfo target

let printEstimations (targets:seq<int>) (casesTestbed:seq<int array>) (splitup:seq<float>) (sb:StringBuilder) =
    let targetsArray = targets.ToArray()
    let casesTestbedArray = casesTestbed.ToArray()
    for i in 0..(targetsArray.Count()-1) do
        let selectedtb = Seq.map (fun (l:int array) -> l.ElementAt i ) casesTestbed
        let selectedt = targetsArray.ElementAt(i)
        printEstimationErrors selectedt selectedtb splitup sb

let printSplitups (progname:string) listOfTargets  (s:SplitupFinder) columnsNames (casesTestbed:seq<int array>) =
    let sbSplitups = new System.Text.StringBuilder()
    sbSplitups.Append("program;") |> ignore
    sbSplitups.AppendLine(String.concat ";" (sanityzeStringSeq columnsNames))  |> ignore
    let sbEstimations = new System.Text.StringBuilder()
    sbEstimations.AppendLine("program;measured;estimated;error;perc")  |> ignore
    let findSplitup target =
        let progname = (getProgNamesAndArgs target).First()
        sbSplitups.AppendFormat("{0};", (sanityzeString progname)) |> ignore
        let p = new Program()
        p.Measures <- (getProgAverages target).ToArray()
        //p.Measures <- (getProgAverages casesRandMemAccess).ToArray()
        s.Target <- p
        if (s.FindSplitup()) then
            let floatToStrings (l:seq<float>) =
                let ni = new System.Globalization.NumberFormatInfo()
                ni.NumberDecimalSeparator <- "."
                ni.NumberGroupSeparator <-""
                Seq.map (fun (f:float) -> f.ToString(ni) ) l
            sbSplitups.AppendLine(String.concat ";" (floatToStrings s.Splitup))  |> ignore
            printEstimations target casesTestbed (s.Splitup) sbEstimations
        else
            System.Console.WriteLine("could not find splitup")
    Seq.iter findSplitup listOfTargets
    let filename = String.Format(@"C:\Users\davide\Documents\GitHub\Energon\data\thrash\splitups{0}.csv", progname)
    System.IO.File.WriteAllText(filename, sbSplitups.ToString())
    let filename2 = String.Format(@"C:\Users\davide\Documents\GitHub\Energon\data\thrash\estimations{0}.csv", progname)
    System.IO.File.WriteAllText(filename2, sbEstimations.ToString())
    Console.WriteLine(String.Format(@"---- done processing {0}", progname))

let getSplitups (progname:string) listOfTargets  (s:SplitupFinder) =
    let findSplitup target =
        let progname = (getProgNamesAndArgs [| target |]).First()
        let p = new Program()
        p.Measures <- (caseToAveragesFinal target ).ToArray()
        s.Target <- p
        if (s.FindSplitup()) then
            s.Splitup
        else
            [| -1.0 |]
    Seq.map findSplitup listOfTargets

let predictConsumption listOfTargets splitups casesTestbed =
    let zipped = Seq.zip listOfTargets splitups
    let calcEst (target,splitup) = getEstimationError target casesTestbed splitup
    Seq.map calcEst zipped

let create_exp_case (basecase:int[]) i =
    [| basecase.[0]+i ; basecase.[1]+i |]

let create_exp_cases exp_base max = 
    let s = seq {
        for i in 0..max do
            yield create_exp_case exp_base i
    }
    Seq.toArray s

let getNth (l:seq<int[]>) n =
    Seq.map (Seq.nth n) l

let getNth2 (l:seq<int[]>) n =
    Seq.map (fun (l2:int[]) -> [| Seq.nth n l2 |]) l



// first arm then target system
let quick = create_exp_cases [| 3717; 3753 |] 6
let merges = create_exp_cases [| 3745; 3760 |] 6
let heap = create_exp_cases [| 3735; 3770 |] 6

let casesRandMemAccess =  [| 3743; 3767 |]
let casesSimpleINT = [| 3744; 3768 |]
let casesSimpleFPU = [| 3332; 3769|]

let casesIozone0 = [| 3804; 3778|]
let casesIozone1 = [| 3805; 3779|]
let casesIozone2 = [| 3806; 3780|]
let casesIozone3 = [| 3807; 3781|]
let casesIozone4 = [| 3808; 3782|]
let casesIozone5 = [| 3809; 3783|]
let casesIozone6 = [| 3810; 3784|]
let casesIozone7 = [| 3811; 3785|]
let casesIozone8 = [| 3812; 3786|]
let casesIozone9 = [| 3813; 3787|]
let casesIozone10 = [| 3814; 3788|]
let casesIozone11 = [| 3815; 3789|]
let casesIozone12 = [| 3816; 3790|]

let iozone = create_exp_cases casesIozone0 12

//let casesTestbed = [| casesRandMemAccess; casesSimpleINT|]
//let casesTestbed = [| casesRandMemAccess; casesSimpleINT; [|3746; 3761 |] |]
//let casesTestbed = [| casesSimpleINT; casesSimpleFPU; [|3746; 3761 |] |]
let casesTestbed = [| casesSimpleINT; casesSimpleFPU; [|3746; 3761 |]; casesIozone1 |]
//let casesTestbed = [|  casesSimpleINT; [|3746; 3761 |] |]
//let casesTestbed = [|  casesSimpleFPU; [|3746; 3761 |] |]
//let casesTestbed = [| casesRandMemAccess; casesSimpleINT; casesSimpleFPU |]
let columnsNames = getColumnsNames casesTestbed

let s = new SplitupFinder()
let testbedAvgs = getTestBedAverages (getNth2 casesTestbed 0)
s.Testbed <- (buildTestBed testbedAvgs)

caseToAveragesFinal 3717

let quickSplitupsArray = Seq.toArray (getSplitups "quick" (getNth quick 0) s)
let mergesSplitupsArray = Seq.toArray (getSplitups "merges" (getNth merges 0) s)
let heapSplitupsArray = Seq.toArray (getSplitups "heap" (getNth heap 0) s)

let iozoneSplitupsArray = Seq.toArray (getSplitups "iozone" (getNth iozone 0) s)

//let quickSplitups = getSplitups "quick" (getNth quick 0) s
//let mergesSplitups = getSplitups "merges" (getNth merges 0) s
//let heapSplitups = getSplitups "heap" (getNth heap 0) s

let consumptionQuick = Seq.toArray (predictConsumption (getNth quick 1) quickSplitupsArray (getNth casesTestbed 1))
let consumptionMerge = Seq.toArray (predictConsumption (getNth merges 1) mergesSplitupsArray (getNth casesTestbed 1))
let consumptionHeap = Seq.toArray (predictConsumption (getNth heap 1) heapSplitupsArray (getNth casesTestbed 1))

let consumptionIozone = Seq.toArray (predictConsumption (getNth iozone 1) iozoneSplitupsArray (getNth casesTestbed 1))

let printSplitup (progname:string) columns (splitups:seq<float []>) (listOfTargets:seq<int>) =
    let sbSplitups = new System.Text.StringBuilder()
    sbSplitups.Append("program;") |> ignore
    sbSplitups.AppendLine(String.concat ";" (sanityzeStringSeq columnsNames))  |> ignore
    let sbEstimations = new System.Text.StringBuilder()
    sbEstimations.AppendLine("program;measured;estimated;error;perc")  |> ignore
    let floatToStrings (l:seq<float>) =
        let ni = new System.Globalization.NumberFormatInfo()
        ni.NumberDecimalSeparator <- "."
        ni.NumberGroupSeparator <-""
        Seq.map (fun (f:float) -> f.ToString(ni) ) l
    let findSplitup (target,splitup) =
        let progname = (getProgNamesAndArgs [|target|]).First()
        sbSplitups.AppendFormat("{0};", (sanityzeString progname)) |> ignore
        sbSplitups.AppendLine(String.concat ";" (floatToStrings splitup))  |> ignore
        printEstimations [| target |] casesTestbed splitup sbEstimations
    let zipped = Seq.zip listOfTargets splitups
    Seq.iter findSplitup zipped 
    let filename = String.Format(@"C:\Users\davide\Documents\GitHub\Energon\data\thrash\splitups{0}.csv", progname)
    System.IO.File.WriteAllText(filename, sbSplitups.ToString())
    let filename2 = String.Format(@"C:\Users\davide\Documents\GitHub\Energon\data\thrash\estimations{0}.csv", progname)
    System.IO.File.WriteAllText(filename2, sbEstimations.ToString())
    Console.WriteLine(String.Format(@"---- done processing {0}", progname))

printSplitup "quick" columnsNames quickSplitupsArray (getNth quick 1)
printSplitup "merges" columnsNames mergesSplitupsArray (getNth merges 1)
printSplitup "heap" columnsNames heapSplitupsArray (getNth heap 1)

caseToAveragesNoJ 3636

getSplitups "merges" [| 3321 |] s

let avg0 = Seq.toArray (caseToAveragesNoJ 3322)
let avg1 = Seq.toArray (caseToAveragesNoJ 3321)
let avg2 = Seq.toArray (caseToAveragesNoJ 3320)
let avg3 = Seq.toArray (caseToAveragesNoJ 3319)
let avg4 = Seq.toArray (caseToAveragesNoJ 3318)
let avg5 = Seq.toArray (caseToAveragesNoJ 3317)

caseToAveragesNoJ 3629
caseToAveragesNoJ 3630
caseToAveragesNoJ 3631
caseToAveragesNoJ 3632

printSplitups "quick" quick s columnsNames casesTestbed
printSplitups "merges" merges s columnsNames casesTestbed
                                                                         
// -------------- testbed using cpuspec ----------- 

let distance l1 l2 =
    let zipped = Seq.zip l1 l2
    let (sum) = Seq.fold (fun (sum) (v1, v2)-> (sum+(v2-v1)*(v2-v1))) (0.) zipped
    Math.Sqrt sum
let average (list) =
    let (sum, count) = list |> Seq.fold (fun (sums, count) (l) -> ((Seq.zip sums l |> Seq.map (fun (v1:float,v2:float)->v1+v2) ), ( Seq.map (fun c -> c + 1.) count ))) (Seq.init (list.First().Count()) (fun _ -> 0.), Seq.init (list.First().Count()) (fun _ -> 0.))
    let l = (Seq.map (fun (s,c) -> s/c) (Seq.zip sum count))
    l.ToArray()
let same s1 s2 =
    Seq.forall2 (fun (f1:float) (f2:float) -> f1=f2) s1 s2

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

let normalizedKmeans (points:float[][]) n =
    let resources = points.ElementAt(0).Count()
    let max (v1:float, v2:float) = if v1> v2 then v1 else v2 
    let maxv = points.Aggregate(Array.init (resources) (fun _ -> 0.), fun state prog ->  (Seq.map max (Seq.zip state prog)).ToArray() ).ToArray() 
    let normVect prog = (Seq.zip prog maxv |> Seq.map (fun (a:float, b:float) -> a/b)).ToArray()
    let normalizedPoints = (Seq.map normVect points).ToArray()
    let c, e = kmeans normalizedPoints n
    let nearest = Seq.map (fun (center:float[]) -> normalizedPoints.OrderBy(fun x -> distance x center).First() ) c
    let getIndex prog =
        let mutable idx = -1
        for i in 0..(normalizedPoints.Count()-1) do
            if (Seq.forall2 (fun v1 v2 -> v1 = v2) prog (normalizedPoints.ElementAt i)) then
                idx <- i
        idx
    (Seq.map (fun (prog:float[]) -> points.ElementAt(getIndex prog) ) nearest).ToArray(), (Seq.map (fun (prog:float[]) -> getIndex prog ) nearest).ToArray()
    
let test1 = [| [| 0.; 1. |]; [| 1. ; 0.|] |]
test1.Aggregate(Array.init (2) (fun _ -> 0.), fun state prog -> (Seq.zip state prog |> Seq.map (fun (v1:float,v2:float) -> Math.Max(v1,v2) )).ToArray()  )

let allprograms = Seq.concat [| iozone_cases; [| casesRandMemAccess |]; [| casesSimpleINT |]; [| casesSimpleFPU |] |]

//let programs = getTestBedAveragesArrays iozone_cases
let programs = getTestBedAveragesArrays allprograms

let c, indices = normalizedKmeans programs 3
let casesTestbed = Seq.map (fun i -> allprograms.ElementAt(i)) indices
let columnsNames = getColumnsNames casesTestbed

let s = new SplitupFinder()
let testbedAvgs = getTestBedAverages casesTestbed
s.Testbed <- (buildTestBed testbedAvgs)

Seq.iter (fun (c:ExperimentAndCases) -> System.Console.WriteLine("{0}:{1}:{2}:{3}", c.Experiment_id, c.Name, c.Id, c.Args)) (db.ExperimentAndCases.Where(fun (e:ExperimentAndCases) -> e.Name.StartsWith("heap")))
let casesHeap4M = [| 3293; 3198 ; |]
let casesHeap16M = [| 3294; 3199; |]
let casesHeap64M = [| 3295; 3200; |]
let casesHeap256M = [| 3296; 3201;  |]
printSplitups "Heapsort_cpuspec3_fpu" [| casesHeap4M; casesHeap16M; casesHeap64M; casesHeap256M |] s columnsNames casesTestbed

let casesMerge4M = [| 3287 ; 3192;  |]
let casesMerge16M = [| 3288; 3193; |]
let casesMerge64M = [| 3289; 3194; |]
let casesMerge256M = [| 3290; 3195; |]
printSplitups "Mergesort_cpuspec3_fpu" [| casesMerge4M; casesMerge16M; casesMerge64M; casesMerge256M |] s columnsNames casesTestbed

Seq.iter (fun (c:ExperimentAndCases) -> System.Console.WriteLine("{0}:{1}:{2}:{3}", c.Experiment_id, c.Name, c.Id, c.Args)) (db.ExperimentAndCases.Where(fun (e:ExperimentAndCases) -> e.Name.StartsWith("quick")))
let casesQuick4M = [| 3281 ; 3181; |]
let casesQuick16M = [| 3282; 3182; |]
let casesQuick64M = [| 3283; 3183; |]
let casesQuick256M = [| 3284; 3184; |]
printSplitups "Quicksort_cpuspec3_fpu" [| casesQuick4M; casesQuick16M; casesQuick64M; casesQuick256M |] s columnsNames casesTestbed

let casesRandMemAccess =  [| 3409; 3415; |]
printSplitups "RandMemAccess_cpuspec3_fpu" [| casesRandMemAccess;|] s columnsNames casesTestbed

let casesSimpleINT = [| 3410; 3416; |]
printSplitups "SimpleINT_cpuspec3_fpu" [| casesSimpleINT; |] s columnsNames casesTestbed

let casesSimpleFPU = [| 3411; 3417;|]
printSplitups "SimpleFPU_cpuspec3_fpu" [| casesSimpleFPU;|] s columnsNames casesTestbed


let casesPi = [| 3412; 3418 |]
printSplitups "Pi_cpuspec3_fpu" [| casesPi |] s columnsNames casesTestbed


// all cpuspec
let specCases = [| cases401; cases435; cases445; cases444; cases410; cases429; cases464; cases458; cases471; cases434; cases453; cases436; cases465; cases483 ; cases462; cases470; cases437; cases433; cases450; cases403; cases482; cases456; cases416; cases999; cases447; cases473; cases400; cases481; cases459; cases998 |]
printSplitups "CPUSPEC_cpuspec3_fpu" specCases s columnsNames casesTestbed


let specCases = [| cases401; cases435; cases445; cases444; cases410; cases429; cases464; cases458; cases471; cases434; cases453; cases436; cases483 ; cases470; cases437; cases433; cases450; cases403; cases482; cases456; cases416; cases999; cases447; cases473; cases400; cases481; cases998 |]
printSplitups "CPUSPEC_cpuspec3_1" specCases s columnsNames casesTestbed

let specCases5 = [| cases401; cases435; cases444; cases410; cases429; cases458; cases434; cases453; cases436; cases483 ; cases462; cases470; cases437; cases433; cases450; cases403; cases482; cases456; cases416; cases999; cases447; cases473; cases400; cases481; cases459 |]
printSplitups "CPUSPEC_cpuspec5" specCases5 s columnsNames casesTestbed

columnsNames.ToArray()


﻿module Energon.Storage.LoaderCE

open System
//open Microsoft.FSharp.Data.TypeProviders
open System.Data.Linq.SqlClient
open System.Linq
open System.Data.Linq
open System.Data.SqlServerCe;
open Energon.Measuring
open Energon.Measuring.Database
open System.Text
open Energon.SQLCE
open System.Collections.Generic


let ExperimentLoaderCE(expID:int, file:string) =
    let getConStr file = 
        let conStr = "Data Source=" + file + ";" in
        conStr;

    let GetLinqContext file = 
        let context = new Measurements(getConStr file)
        if (context.DatabaseExists() = false) then
             context.CreateDatabase()
        context
    
    let db = GetLinqContext file
    
    let dbExperiment = db.Experiments.Where(fun (x:Experiments) -> x.Id = expID).First()
    let dbCases = db.ExperimentCases.Where(fun (x:ExperimentCases) -> x.Experiment_id = expID)
    let runsOfCase (case:ExperimentCases) =
        db.ExperimentRuns.Where(fun (x:ExperimentRuns) -> x.Experiment_case_id = case.Experiment_id)
    let sensorsOfRun (run:ExperimentRuns) =
        db.Sensors.Where(fun (x:Sensors) -> x.Experiment_run_id = run.Id)
    // the list of sensors this experient is using
    let sensors = new List<DatabaseSensor>()
    let sensorToSensorClass (s:Sensors) =
        db.SensorClasses.Where(fun (cl:SensorClasses) -> cl.Id = s.Sensor_class_id)
    let sensorClassToSensor (s:SensorClasses) =
        let sensArray = sensors.ToArray()
        let sens = sensArray.Where(fun (x:DatabaseSensor) -> x.ID = s.Id)
        if (sens.Count() > 0) then
            let newSens = new DatabaseSensor(s.SensorName, s.Id)
            sensors.Add(newSens)
            newSens
        else
            sens.First()

    let sensorToSensorClass (s:Sensors) =
        db.SensorClasses.Where(fun (x:SensorClasses) -> x.Id = s.Sensor_class_id).First()

    let runseqseq = Seq.map runsOfCase dbCases 
    let runseq2senseqseq (runseq:seq<ExperimentRuns>) =
        runseq |> Seq.map (fun (x:ExperimentRuns) ->
                sensorsOfRun x
            )

    let handleSensors (s:Sensors) =
        let sensRes = sensors.Where(fun (x:DatabaseSensor) -> x.ID = s.Sensor_class_id)
        if (sensRes.Count() = 0) then
            let cl = sensorToSensorClass s
            let newSens = new DatabaseSensor(cl.SensorName, cl.Id)
            sensors.Add(newSens)

    runseqseq |> Seq.iter (fun (runseq:IQueryable<ExperimentRuns>) -> 
            let sensseqseq = runseq2senseqseq runseq
            sensseqseq |> Seq.iter ( fun (sensseq:IQueryable<Sensors>) -> 
                Seq.iter handleSensors sensseq
            )
        )  
    let exp = new DatabaseExperiment(dbExperiment.Name, sensors, dbExperiment.Iter.Value, Seq.empty, Seq.empty, expID)
    let sensorSeq = seq {
            for s in sensors do yield s:>GenericSensor
        }
    dbCases |> Seq.iter (fun (x:ExperimentCases) ->
            let split = [";"].ToArray()
            let args = x.Args.Split(split, StringSplitOptions.RemoveEmptyEntries)
            let c = new DatabaseExperimentCase(sensorSeq, exp.IterCount,  args |> Seq.map (fun x -> x :> obj) , x.Id)
            exp.ExperimentCases.Add(c)
            let dbRuns = runsOfCase x
            dbRuns |> Seq.iter ( fun (r:ExperimentRuns) ->
                let run = new DatabaseExperimentRun(sensorSeq, r.Id)
                c.ExperimentRuns.Add(run)

            )
        )

    



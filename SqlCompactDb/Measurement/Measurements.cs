﻿#pragma warning disable 1591
//------------------------------------------------------------------------------
// <auto-generated>
//     This code was generated by a tool.
//     Runtime Version:4.0.30319.17379
//
//     Changes to this file may cause incorrect behavior and will be lost if
//     the code is regenerated.
// </auto-generated>
//------------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Data.Linq;
using System.Data.Linq.Mapping;
using System.Linq;
using System.Linq.Expressions;
using System.Reflection;


namespace Energon.SQLCE
{

    public partial class Measurements : System.Data.Linq.DataContext
    {

        private static System.Data.Linq.Mapping.MappingSource mappingSource = new AttributeMappingSource();

        #region Extensibility Method Definitions
        partial void OnCreated();
        partial void InsertEnvironment(Environment instance);
        partial void UpdateEnvironment(Environment instance);
        partial void DeleteEnvironment(Environment instance);
        partial void InsertExperimentCases(ExperimentCases instance);
        partial void UpdateExperimentCases(ExperimentCases instance);
        partial void DeleteExperimentCases(ExperimentCases instance);
        partial void InsertExperimentRuns(ExperimentRuns instance);
        partial void UpdateExperimentRuns(ExperimentRuns instance);
        partial void DeleteExperimentRuns(ExperimentRuns instance);
        partial void InsertExperiments(Experiments instance);
        partial void UpdateExperiments(Experiments instance);
        partial void DeleteExperiments(Experiments instance);
        partial void InsertMeasurements1(Measurements1 instance);
        partial void UpdateMeasurements1(Measurements1 instance);
        partial void DeleteMeasurements1(Measurements1 instance);
        partial void InsertSensorClasses(SensorClasses instance);
        partial void UpdateSensorClasses(SensorClasses instance);
        partial void DeleteSensorClasses(SensorClasses instance);
        partial void InsertSensors(Sensors instance);
        partial void UpdateSensors(Sensors instance);
        partial void DeleteSensors(Sensors instance);
        #endregion

        public Measurements(string connection) :
            base(connection, mappingSource)
        {
            OnCreated();
        }

        public Measurements(System.Data.IDbConnection connection) :
            base(connection, mappingSource)
        {
            OnCreated();
        }

        public Measurements(string connection, System.Data.Linq.Mapping.MappingSource mappingSource) :
            base(connection, mappingSource)
        {
            OnCreated();
        }

        public Measurements(System.Data.IDbConnection connection, System.Data.Linq.Mapping.MappingSource mappingSource) :
            base(connection, mappingSource)
        {
            OnCreated();
        }

        public System.Data.Linq.Table<Environment> Environment
        {
            get
            {
                return this.GetTable<Environment>();
            }
        }

        public System.Data.Linq.Table<ExperimentCases> ExperimentCases
        {
            get
            {
                return this.GetTable<ExperimentCases>();
            }
        }

        public System.Data.Linq.Table<ExperimentRuns> ExperimentRuns
        {
            get
            {
                return this.GetTable<ExperimentRuns>();
            }
        }

        public System.Data.Linq.Table<Experiments> Experiments
        {
            get
            {
                return this.GetTable<Experiments>();
            }
        }

        public System.Data.Linq.Table<Measurements1> Measurements1
        {
            get
            {
                return this.GetTable<Measurements1>();
            }
        }

        public System.Data.Linq.Table<SensorClasses> SensorClasses
        {
            get
            {
                return this.GetTable<SensorClasses>();
            }
        }

        public System.Data.Linq.Table<Sensors> Sensors
        {
            get
            {
                return this.GetTable<Sensors>();
            }
        }
    }

    [global::System.Data.Linq.Mapping.TableAttribute()]
    public partial class Environment : INotifyPropertyChanging, INotifyPropertyChanged
    {

        private static PropertyChangingEventArgs emptyChangingEventArgs = new PropertyChangingEventArgs(String.Empty);

        private string _Name;

        private string _Note;

        private int _Id;

        #region Extensibility Method Definitions
        partial void OnLoaded();
        partial void OnValidate(System.Data.Linq.ChangeAction action);
        partial void OnCreated();
        partial void OnNameChanging(string value);
        partial void OnNameChanged();
        partial void OnNoteChanging(string value);
        partial void OnNoteChanged();
        partial void OnIdChanging(int value);
        partial void OnIdChanged();
        #endregion

        public Environment()
        {
            OnCreated();
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "name", Storage = "_Name", DbType = "NVarChar(256)")]
        public string Name
        {
            get
            {
                return this._Name;
            }
            set
            {
                if ((this._Name != value))
                {
                    this.OnNameChanging(value);
                    this.SendPropertyChanging();
                    this._Name = value;
                    this.SendPropertyChanged("Name");
                    this.OnNameChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "note", Storage = "_Note", DbType = "NText", UpdateCheck = UpdateCheck.Never)]
        public string Note
        {
            get
            {
                return this._Note;
            }
            set
            {
                if ((this._Note != value))
                {
                    this.OnNoteChanging(value);
                    this.SendPropertyChanging();
                    this._Note = value;
                    this.SendPropertyChanged("Note");
                    this.OnNoteChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "id", Storage = "_Id", AutoSync = AutoSync.OnInsert, DbType = "Int NOT NULL IDENTITY", IsPrimaryKey = true, IsDbGenerated = true)]
        public int Id
        {
            get
            {
                return this._Id;
            }
            set
            {
                if ((this._Id != value))
                {
                    this.OnIdChanging(value);
                    this.SendPropertyChanging();
                    this._Id = value;
                    this.SendPropertyChanged("Id");
                    this.OnIdChanged();
                }
            }
        }

        public event PropertyChangingEventHandler PropertyChanging;

        public event PropertyChangedEventHandler PropertyChanged;

        protected virtual void SendPropertyChanging()
        {
            if ((this.PropertyChanging != null))
            {
                this.PropertyChanging(this, emptyChangingEventArgs);
            }
        }

        protected virtual void SendPropertyChanged(String propertyName)
        {
            if ((this.PropertyChanged != null))
            {
                this.PropertyChanged(this, new PropertyChangedEventArgs(propertyName));
            }
        }
    }

    [global::System.Data.Linq.Mapping.TableAttribute()]
    public partial class ExperimentCases : INotifyPropertyChanging, INotifyPropertyChanged
    {

        private static PropertyChangingEventArgs emptyChangingEventArgs = new PropertyChangingEventArgs(String.Empty);

        private int _Id;

        private string _Args;

        private int _Experiment_id;

        #region Extensibility Method Definitions
        partial void OnLoaded();
        partial void OnValidate(System.Data.Linq.ChangeAction action);
        partial void OnCreated();
        partial void OnIdChanging(int value);
        partial void OnIdChanged();
        partial void OnArgsChanging(string value);
        partial void OnArgsChanged();
        partial void OnExperiment_idChanging(int value);
        partial void OnExperiment_idChanged();
        #endregion

        public ExperimentCases()
        {
            OnCreated();
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "id", Storage = "_Id", AutoSync = AutoSync.OnInsert, DbType = "Int NOT NULL IDENTITY", IsPrimaryKey = true, IsDbGenerated = true)]
        public int Id
        {
            get
            {
                return this._Id;
            }
            set
            {
                if ((this._Id != value))
                {
                    this.OnIdChanging(value);
                    this.SendPropertyChanging();
                    this._Id = value;
                    this.SendPropertyChanged("Id");
                    this.OnIdChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "args", Storage = "_Args", DbType = "NVarChar(4000)")]
        public string Args
        {
            get
            {
                return this._Args;
            }
            set
            {
                if ((this._Args != value))
                {
                    this.OnArgsChanging(value);
                    this.SendPropertyChanging();
                    this._Args = value;
                    this.SendPropertyChanged("Args");
                    this.OnArgsChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "experiment_id", Storage = "_Experiment_id", DbType = "Int NOT NULL")]
        public int Experiment_id
        {
            get
            {
                return this._Experiment_id;
            }
            set
            {
                if ((this._Experiment_id != value))
                {
                    this.OnExperiment_idChanging(value);
                    this.SendPropertyChanging();
                    this._Experiment_id = value;
                    this.SendPropertyChanged("Experiment_id");
                    this.OnExperiment_idChanged();
                }
            }
        }

        public event PropertyChangingEventHandler PropertyChanging;

        public event PropertyChangedEventHandler PropertyChanged;

        protected virtual void SendPropertyChanging()
        {
            if ((this.PropertyChanging != null))
            {
                this.PropertyChanging(this, emptyChangingEventArgs);
            }
        }

        protected virtual void SendPropertyChanged(String propertyName)
        {
            if ((this.PropertyChanged != null))
            {
                this.PropertyChanged(this, new PropertyChangedEventArgs(propertyName));
            }
        }
    }

    [global::System.Data.Linq.Mapping.TableAttribute()]
    public partial class ExperimentRuns : INotifyPropertyChanging, INotifyPropertyChanged
    {

        private static PropertyChangingEventArgs emptyChangingEventArgs = new PropertyChangingEventArgs(String.Empty);

        private string _Args;

        private System.Nullable<System.DateTime> _Start;

        private System.Nullable<System.DateTime> _End;

        private int _Id;

        private int _Experiment_case_id;

        #region Extensibility Method Definitions
        partial void OnLoaded();
        partial void OnValidate(System.Data.Linq.ChangeAction action);
        partial void OnCreated();
        partial void OnArgsChanging(string value);
        partial void OnArgsChanged();
        partial void OnStartChanging(System.Nullable<System.DateTime> value);
        partial void OnStartChanged();
        partial void OnEndChanging(System.Nullable<System.DateTime> value);
        partial void OnEndChanged();
        partial void OnIdChanging(int value);
        partial void OnIdChanged();
        partial void OnExperiment_case_idChanging(int value);
        partial void OnExperiment_case_idChanged();
        #endregion

        public ExperimentRuns()
        {
            OnCreated();
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "args", Storage = "_Args", DbType = "NVarChar(4000)")]
        public string Args
        {
            get
            {
                return this._Args;
            }
            set
            {
                if ((this._Args != value))
                {
                    this.OnArgsChanging(value);
                    this.SendPropertyChanging();
                    this._Args = value;
                    this.SendPropertyChanged("Args");
                    this.OnArgsChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "start", Storage = "_Start", DbType = "DateTime")]
        public System.Nullable<System.DateTime> Start
        {
            get
            {
                return this._Start;
            }
            set
            {
                if ((this._Start != value))
                {
                    this.OnStartChanging(value);
                    this.SendPropertyChanging();
                    this._Start = value;
                    this.SendPropertyChanged("Start");
                    this.OnStartChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "end", Storage = "_End", DbType = "DateTime")]
        public System.Nullable<System.DateTime> End
        {
            get
            {
                return this._End;
            }
            set
            {
                if ((this._End != value))
                {
                    this.OnEndChanging(value);
                    this.SendPropertyChanging();
                    this._End = value;
                    this.SendPropertyChanged("End");
                    this.OnEndChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "id", Storage = "_Id", AutoSync = AutoSync.OnInsert, DbType = "Int NOT NULL IDENTITY", IsPrimaryKey = true, IsDbGenerated = true)]
        public int Id
        {
            get
            {
                return this._Id;
            }
            set
            {
                if ((this._Id != value))
                {
                    this.OnIdChanging(value);
                    this.SendPropertyChanging();
                    this._Id = value;
                    this.SendPropertyChanged("Id");
                    this.OnIdChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "experiment_case_id", Storage = "_Experiment_case_id", DbType = "Int NOT NULL")]
        public int Experiment_case_id
        {
            get
            {
                return this._Experiment_case_id;
            }
            set
            {
                if ((this._Experiment_case_id != value))
                {
                    this.OnExperiment_case_idChanging(value);
                    this.SendPropertyChanging();
                    this._Experiment_case_id = value;
                    this.SendPropertyChanged("Experiment_case_id");
                    this.OnExperiment_case_idChanged();
                }
            }
        }

        public event PropertyChangingEventHandler PropertyChanging;

        public event PropertyChangedEventHandler PropertyChanged;

        protected virtual void SendPropertyChanging()
        {
            if ((this.PropertyChanging != null))
            {
                this.PropertyChanging(this, emptyChangingEventArgs);
            }
        }

        protected virtual void SendPropertyChanged(String propertyName)
        {
            if ((this.PropertyChanged != null))
            {
                this.PropertyChanged(this, new PropertyChangedEventArgs(propertyName));
            }
        }
    }

    [global::System.Data.Linq.Mapping.TableAttribute()]
    public partial class Experiments : INotifyPropertyChanging, INotifyPropertyChanged
    {

        private static PropertyChangingEventArgs emptyChangingEventArgs = new PropertyChangingEventArgs(String.Empty);

        private string _Name;

        private string _Note;

        private int _Id;

        private System.Nullable<int> _Iter;

        private string _ArgNames;

        #region Extensibility Method Definitions
        partial void OnLoaded();
        partial void OnValidate(System.Data.Linq.ChangeAction action);
        partial void OnCreated();
        partial void OnNameChanging(string value);
        partial void OnNameChanged();
        partial void OnNoteChanging(string value);
        partial void OnNoteChanged();
        partial void OnIdChanging(int value);
        partial void OnIdChanged();
        partial void OnIterChanging(System.Nullable<int> value);
        partial void OnIterChanged();
        partial void OnArgNamesChanging(string value);
        partial void OnArgNamesChanged();
        #endregion

        public Experiments()
        {
            OnCreated();
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "name", Storage = "_Name", DbType = "NVarChar(4000)")]
        public string Name
        {
            get
            {
                return this._Name;
            }
            set
            {
                if ((this._Name != value))
                {
                    this.OnNameChanging(value);
                    this.SendPropertyChanging();
                    this._Name = value;
                    this.SendPropertyChanged("Name");
                    this.OnNameChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "note", Storage = "_Note", DbType = "NText", UpdateCheck = UpdateCheck.Never)]
        public string Note
        {
            get
            {
                return this._Note;
            }
            set
            {
                if ((this._Note != value))
                {
                    this.OnNoteChanging(value);
                    this.SendPropertyChanging();
                    this._Note = value;
                    this.SendPropertyChanged("Note");
                    this.OnNoteChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "id", Storage = "_Id", AutoSync = AutoSync.OnInsert, DbType = "Int NOT NULL IDENTITY", IsPrimaryKey = true, IsDbGenerated = true)]
        public int Id
        {
            get
            {
                return this._Id;
            }
            set
            {
                if ((this._Id != value))
                {
                    this.OnIdChanging(value);
                    this.SendPropertyChanging();
                    this._Id = value;
                    this.SendPropertyChanged("Id");
                    this.OnIdChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "iter", Storage = "_Iter", DbType = "Int")]
        public System.Nullable<int> Iter
        {
            get
            {
                return this._Iter;
            }
            set
            {
                if ((this._Iter != value))
                {
                    this.OnIterChanging(value);
                    this.SendPropertyChanging();
                    this._Iter = value;
                    this.SendPropertyChanged("Iter");
                    this.OnIterChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "argNames", Storage = "_ArgNames", DbType = "NText", UpdateCheck = UpdateCheck.Never)]
        public string ArgNames
        {
            get
            {
                return this._ArgNames;
            }
            set
            {
                if ((this._ArgNames != value))
                {
                    this.OnArgNamesChanging(value);
                    this.SendPropertyChanging();
                    this._ArgNames = value;
                    this.SendPropertyChanged("ArgNames");
                    this.OnArgNamesChanged();
                }
            }
        }

        public event PropertyChangingEventHandler PropertyChanging;

        public event PropertyChangedEventHandler PropertyChanged;

        protected virtual void SendPropertyChanging()
        {
            if ((this.PropertyChanging != null))
            {
                this.PropertyChanging(this, emptyChangingEventArgs);
            }
        }

        protected virtual void SendPropertyChanged(String propertyName)
        {
            if ((this.PropertyChanged != null))
            {
                this.PropertyChanged(this, new PropertyChangedEventArgs(propertyName));
            }
        }
    }

    [global::System.Data.Linq.Mapping.TableAttribute(Name = "Measurements")]
    public partial class Measurements1 : INotifyPropertyChanging, INotifyPropertyChanged
    {

        private static PropertyChangingEventArgs emptyChangingEventArgs = new PropertyChangingEventArgs(String.Empty);

        private double _Value;

        private System.Data.Linq.Binary _Row;

        private int _Id;

        private int _Sensor_id;

        private System.DateTime _Timestamp;

        #region Extensibility Method Definitions
        partial void OnLoaded();
        partial void OnValidate(System.Data.Linq.ChangeAction action);
        partial void OnCreated();
        partial void OnValueChanging(double value);
        partial void OnValueChanged();
        partial void OnRowChanging(System.Data.Linq.Binary value);
        partial void OnRowChanged();
        partial void OnIdChanging(int value);
        partial void OnIdChanged();
        partial void OnSensor_idChanging(int value);
        partial void OnSensor_idChanged();
        partial void OnTimestampChanging(System.DateTime value);
        partial void OnTimestampChanged();
        #endregion

        public Measurements1()
        {
            OnCreated();
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "value", Storage = "_Value", DbType = "Float NOT NULL")]
        public double Value
        {
            get
            {
                return this._Value;
            }
            set
            {
                if ((this._Value != value))
                {
                    this.OnValueChanging(value);
                    this.SendPropertyChanging();
                    this._Value = value;
                    this.SendPropertyChanged("Value");
                    this.OnValueChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "row", Storage = "_Row", DbType = "VarBinary(256)", CanBeNull = true)]
        public System.Data.Linq.Binary Row
        {
            get
            {
                return this._Row;
            }
            set
            {
                if ((this._Row != value))
                {
                    this.OnRowChanging(value);
                    this.SendPropertyChanging();
                    this._Row = value;
                    this.SendPropertyChanged("Row");
                    this.OnRowChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "id", Storage = "_Id", AutoSync = AutoSync.OnInsert, DbType = "Int NOT NULL IDENTITY", IsPrimaryKey = true, IsDbGenerated = true)]
        public int Id
        {
            get
            {
                return this._Id;
            }
            set
            {
                if ((this._Id != value))
                {
                    this.OnIdChanging(value);
                    this.SendPropertyChanging();
                    this._Id = value;
                    this.SendPropertyChanged("Id");
                    this.OnIdChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "sensor_id", Storage = "_Sensor_id", DbType = "Int NOT NULL")]
        public int Sensor_id
        {
            get
            {
                return this._Sensor_id;
            }
            set
            {
                if ((this._Sensor_id != value))
                {
                    this.OnSensor_idChanging(value);
                    this.SendPropertyChanging();
                    this._Sensor_id = value;
                    this.SendPropertyChanged("Sensor_id");
                    this.OnSensor_idChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "timestamp", Storage = "_Timestamp", DbType = "DateTime NOT NULL")]
        public System.DateTime Timestamp
        {
            get
            {
                return this._Timestamp;
            }
            set
            {
                if ((this._Timestamp != value))
                {
                    this.OnTimestampChanging(value);
                    this.SendPropertyChanging();
                    this._Timestamp = value;
                    this.SendPropertyChanged("Timestamp");
                    this.OnTimestampChanged();
                }
            }
        }

        public event PropertyChangingEventHandler PropertyChanging;

        public event PropertyChangedEventHandler PropertyChanged;

        protected virtual void SendPropertyChanging()
        {
            if ((this.PropertyChanging != null))
            {
                this.PropertyChanging(this, emptyChangingEventArgs);
            }
        }

        protected virtual void SendPropertyChanged(String propertyName)
        {
            if ((this.PropertyChanged != null))
            {
                this.PropertyChanged(this, new PropertyChangedEventArgs(propertyName));
            }
        }
    }

    [global::System.Data.Linq.Mapping.TableAttribute()]
    public partial class SensorClasses : INotifyPropertyChanging, INotifyPropertyChanged
    {

        private static PropertyChangingEventArgs emptyChangingEventArgs = new PropertyChangingEventArgs(String.Empty);

        private string _Note;

        private string _SensorName;

        private int _Id;

        #region Extensibility Method Definitions
        partial void OnLoaded();
        partial void OnValidate(System.Data.Linq.ChangeAction action);
        partial void OnCreated();
        partial void OnNoteChanging(string value);
        partial void OnNoteChanged();
        partial void OnSensorNameChanging(string value);
        partial void OnSensorNameChanged();
        partial void OnIdChanging(int value);
        partial void OnIdChanged();
        #endregion

        public SensorClasses()
        {
            OnCreated();
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "note", Storage = "_Note", DbType = "NText", UpdateCheck = UpdateCheck.Never)]
        public string Note
        {
            get
            {
                return this._Note;
            }
            set
            {
                if ((this._Note != value))
                {
                    this.OnNoteChanging(value);
                    this.SendPropertyChanging();
                    this._Note = value;
                    this.SendPropertyChanged("Note");
                    this.OnNoteChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Storage = "_SensorName", DbType = "NVarChar(256) NOT NULL", CanBeNull = false, IsPrimaryKey = true)]
        public string SensorName
        {
            get
            {
                return this._SensorName;
            }
            set
            {
                if ((this._SensorName != value))
                {
                    this.OnSensorNameChanging(value);
                    this.SendPropertyChanging();
                    this._SensorName = value;
                    this.SendPropertyChanged("SensorName");
                    this.OnSensorNameChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "id", Storage = "_Id", AutoSync = AutoSync.OnInsert, DbType = "Int NOT NULL IDENTITY", IsPrimaryKey = true, IsDbGenerated = true)]
        public int Id
        {
            get
            {
                return this._Id;
            }
            set
            {
                if ((this._Id != value))
                {
                    this.OnIdChanging(value);
                    this.SendPropertyChanging();
                    this._Id = value;
                    this.SendPropertyChanged("Id");
                    this.OnIdChanged();
                }
            }
        }

        public event PropertyChangingEventHandler PropertyChanging;

        public event PropertyChangedEventHandler PropertyChanged;

        protected virtual void SendPropertyChanging()
        {
            if ((this.PropertyChanging != null))
            {
                this.PropertyChanging(this, emptyChangingEventArgs);
            }
        }

        protected virtual void SendPropertyChanged(String propertyName)
        {
            if ((this.PropertyChanged != null))
            {
                this.PropertyChanged(this, new PropertyChangedEventArgs(propertyName));
            }
        }
    }

    [global::System.Data.Linq.Mapping.TableAttribute()]
    public partial class Sensors : INotifyPropertyChanging, INotifyPropertyChanged
    {

        private static PropertyChangingEventArgs emptyChangingEventArgs = new PropertyChangingEventArgs(String.Empty);

        private int _Experiment_run_id;

        private int _Sensor_class_id;

        private int _Id;

        #region Extensibility Method Definitions
        partial void OnLoaded();
        partial void OnValidate(System.Data.Linq.ChangeAction action);
        partial void OnCreated();
        partial void OnExperiment_run_idChanging(int value);
        partial void OnExperiment_run_idChanged();
        partial void OnSensor_class_idChanging(int value);
        partial void OnSensor_class_idChanged();
        partial void OnIdChanging(int value);
        partial void OnIdChanged();
        #endregion

        public Sensors()
        {
            OnCreated();
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "experiment_run_id", Storage = "_Experiment_run_id", DbType = "Int NOT NULL")]
        public int Experiment_run_id
        {
            get
            {
                return this._Experiment_run_id;
            }
            set
            {
                if ((this._Experiment_run_id != value))
                {
                    this.OnExperiment_run_idChanging(value);
                    this.SendPropertyChanging();
                    this._Experiment_run_id = value;
                    this.SendPropertyChanged("Experiment_run_id");
                    this.OnExperiment_run_idChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "sensor_class_id", Storage = "_Sensor_class_id", DbType = "Int NOT NULL")]
        public int Sensor_class_id
        {
            get
            {
                return this._Sensor_class_id;
            }
            set
            {
                if ((this._Sensor_class_id != value))
                {
                    this.OnSensor_class_idChanging(value);
                    this.SendPropertyChanging();
                    this._Sensor_class_id = value;
                    this.SendPropertyChanged("Sensor_class_id");
                    this.OnSensor_class_idChanged();
                }
            }
        }

        [global::System.Data.Linq.Mapping.ColumnAttribute(Name = "id", Storage = "_Id", AutoSync = AutoSync.OnInsert, DbType = "Int NOT NULL IDENTITY", IsPrimaryKey = true, IsDbGenerated = true)]
        public int Id
        {
            get
            {
                return this._Id;
            }
            set
            {
                if ((this._Id != value))
                {
                    this.OnIdChanging(value);
                    this.SendPropertyChanging();
                    this._Id = value;
                    this.SendPropertyChanged("Id");
                    this.OnIdChanged();
                }
            }
        }

        public event PropertyChangingEventHandler PropertyChanging;

        public event PropertyChangedEventHandler PropertyChanged;

        protected virtual void SendPropertyChanging()
        {
            if ((this.PropertyChanging != null))
            {
                this.PropertyChanging(this, emptyChangingEventArgs);
            }
        }

        protected virtual void SendPropertyChanged(String propertyName)
        {
            if ((this.PropertyChanged != null))
            {
                this.PropertyChanged(this, new PropertyChangedEventArgs(propertyName));
            }
        }
    }
#pragma warning restore 1591
}
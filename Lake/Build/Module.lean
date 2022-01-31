/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.Build.Target
import Lake.Build.Actions
import Lake.Build.Recursive
import Lake.Build.TargetTypes
import Lake.Config.Package
import Lake.Build.Targets

open System
open Lean hiding SearchPath

namespace Lake

-- # Targets

structure OleanAndC where
  oleanFile : FilePath
  cFile : FilePath
  deriving Inhabited, Repr

namespace OleanAndC

protected def getMTime (self : OleanAndC) : IO MTime := do
  return mixTrace (← getMTime self.oleanFile) (← getMTime self.cFile)

instance : GetMTime OleanAndC := ⟨OleanAndC.getMTime⟩

protected def computeHash (self : OleanAndC) : IO Hash := do
  return mixTrace (← computeHash self.oleanFile) (← computeHash self.cFile)

instance : ComputeHash OleanAndC IO := ⟨OleanAndC.computeHash⟩

protected def checkExists (self : OleanAndC) : BaseIO Bool := do
  return (← checkExists self.oleanFile) && (← checkExists self.cFile)

instance : CheckExists OleanAndC := ⟨OleanAndC.checkExists⟩

end OleanAndC

abbrev OleanAndCTarget := BuildTarget OleanAndC

namespace OleanAndCTarget

abbrev oleanFile (self : OleanAndCTarget) := self.info.oleanFile
def oleanTarget (self : OleanAndCTarget) : FileTarget :=
  Target.mk self.oleanFile do self.bindSync fun i _ => computeTrace i.oleanFile

abbrev cFile (self : OleanAndCTarget) := self.info.cFile
def cTarget (self : OleanAndCTarget) : FileTarget :=
  Target.mk self.cFile do self.bindSync fun i _ => computeTrace i.cFile

end OleanAndCTarget

structure ActiveOleanAndCTargets where
  oleanTarget : ActiveFileTarget
  cTarget : ActiveFileTarget
  deriving Inhabited

namespace ActiveOleanAndCTargets
abbrev oleanFile (self : ActiveOleanAndCTargets) := self.oleanTarget.info
abbrev cFile (self : ActiveOleanAndCTargets) := self.cTarget.info
end ActiveOleanAndCTargets

/--
An active module `.olean` and `.c` target consists of a single task that
builds both with two dependent targets that compute their individual traces.
-/
abbrev ActiveOleanAndCTarget := ActiveBuildTarget ActiveOleanAndCTargets

namespace ActiveOleanAndCTarget

abbrev oleanFile (self : ActiveOleanAndCTarget) := self.info.oleanFile
abbrev oleanTarget (self : ActiveOleanAndCTarget) := self.info.oleanTarget

abbrev cFile (self : ActiveOleanAndCTarget) := self.info.cFile
abbrev cTarget (self : ActiveOleanAndCTarget) := self.info.cTarget

end ActiveOleanAndCTarget

def OleanAndCTarget.activate (self : OleanAndCTarget) : SchedulerM ActiveOleanAndCTarget := do
  let t ← BuildTarget.activate self
  let oleanTask ← t.bindSync fun info depTrace => do
    return mixTrace (← computeTrace info.oleanFile) depTrace
  let cTask ← t.bindSync fun info _ => do
    return mixTrace (← computeTrace info.cFile) (← getLeanTrace)
  return t.withInfo {
    oleanTarget := ActiveTarget.mk self.oleanFile oleanTask
    cTarget := ActiveTarget.mk self.cFile cTask
  }

-- # Module Builders

def moduleTarget
[CheckExists i] [GetMTime i] [ComputeHash i m] [MonadLiftT m BuildM] (info : i)
(leanFile traceFile : FilePath) (contents : String) (depTarget : BuildTarget x)
(build : BuildM PUnit) : BuildTarget i :=
  Target.mk info <| depTarget.bindOpaqueSync fun depTrace => do
    let srcTrace : BuildTrace := ⟨Hash.ofString contents, ← getMTime leanFile⟩
    let fullTrace := (← getLeanTrace).mix <| srcTrace.mix depTrace
    let upToDate ← fullTrace.checkAgainstFile info traceFile
    unless upToDate do
      build
    fullTrace.writeToFile traceFile
    depTrace

def moduleOleanAndCTarget
(leanFile cFile oleanFile traceFile : FilePath)
(contents : String)  (depTarget : BuildTarget x)
(rootDir : FilePath := ".") (leanArgs : Array String := #[]) (precompiledPath : SearchPath := ∅) : OleanAndCTarget :=
  moduleTarget (OleanAndC.mk oleanFile cFile) leanFile traceFile contents depTarget do
    compileOleanAndC leanFile oleanFile cFile (← getOleanPath) rootDir leanArgs (← getLean) precompiledPath

def moduleOleanTarget
(leanFile oleanFile traceFile : FilePath)
(contents : String) (depTarget : BuildTarget x)
(rootDir : FilePath := ".") (leanArgs : Array String := #[]) : FileTarget :=
  let target := moduleTarget oleanFile leanFile traceFile contents depTarget do
    compileOlean leanFile oleanFile (← getOleanPath) rootDir leanArgs (← getLean)
  target.withTask do target.bindSync fun oleanFile depTrace => do
    return mixTrace (← computeTrace oleanFile) depTrace

-- NOTE: `loadLibs` may (transitively) load other precompiled libraries;
-- `precompiledPath` must contain the directories of all these libraries (on Windows)
protected def Package.moduleOleanAndCTargetOnly (self : Package)
(mod : Name) (leanFile : FilePath) (contents : String) (loadLibs : Array FilePath) (precompiledPath : SearchPath) (depTarget : BuildTarget x) :=
  let cFile := self.modToC mod
  let oleanFile := self.modToOlean mod
  let traceFile := self.modToTraceFile mod
  let args := self.moreLeanArgs ++ loadLibs.map (s!"--load-dynlib={·}")
  moduleOleanAndCTarget leanFile cFile oleanFile traceFile contents
    depTarget self.rootDir args precompiledPath

protected def Package.moduleOleanTargetOnly (self : Package)
(mod : Name) (leanFile : FilePath) (contents : String) (depTarget : BuildTarget x) :=
  let oleanFile := self.modToOlean mod
  let traceFile := self.modToTraceFile mod
  moduleOleanTarget leanFile oleanFile traceFile contents depTarget
    self.rootDir self.moreLeanArgs

-- # Recursive Building

structure ModuleInfo where
  pkg : Package
  name : Name

def ModuleInfo.srcFile (self : ModuleInfo) : FilePath :=
  self.pkg.modToSrc self.name

structure ModuleBuildCfg where
  buildSharedLibs : Bool := false

abbrev ModuleBuildM (α) :=
  -- equivalent to `ReaderT ModuleBuildCfg <| RBTopT (cmp := Name.quickCmp) Name α BuildM`.
  -- phrased this way to use `NameMap`
  EStateT (List Name) (NameMap α) <| ReaderT ModuleBuildCfg BuildM

-- NOTE: `buildC` should be considered a *request* from external users.
-- C files may be built regardless because of precompilation, but this fact is opaque to the caller.
structure ActiveModuleTargets (buildC : Bool) where
  mod : Name
  leanOutputTarget : if buildC then ActiveOleanAndCTarget else ActiveFileTarget
  sharedLibTarget? : Option ActiveFileTarget := none
  -- NOTE: used only on Windows
  allLoadLibs : Std.RBTree String compare := ∅

instance (buildC) : Inhabited (ActiveModuleTargets buildC) where
  default := {
    mod := default
    leanOutputTarget := match (generalizing := true) buildC with
      | false => (default : ActiveFileTarget)
      | true  => (default : ActiveOleanAndCTarget)
  }

abbrev ActiveModuleTarget (buildC : Bool) := ActiveBuildTarget (ActiveModuleTargets buildC)

abbrev RecModuleBuild (buildC : Bool) := RecBuild ModuleInfo (ActiveModuleTarget buildC) (ModuleBuildM (ActiveModuleTarget buildC))

variable {buildC : Bool}

def ActiveModuleTargets.oleanTarget (self : ActiveModuleTargets buildC) : ActiveFileTarget :=
  match (generalizing := true) buildC with
  | true  => self.leanOutputTarget.oleanTarget
  | false => self.leanOutputTarget

def recBuildModuleTargetsWithLocalImports (depTarget : ActiveBuildTarget x)
: RecModuleBuild buildC := fun info@{ pkg, name := mod } recurse => do
  let contents ← IO.FS.readFile info.srcFile
  let (imports, _, _) ← Elab.parseImports contents info.srcFile.toString
  let mut cfg ← readThe ModuleBuildCfg
  if !cfg.buildSharedLibs && pkg.config.precompileModules then
    cfg := { cfg with buildSharedLibs := true }
  -- we construct the import targets even if a rebuild is not required
  -- because other build processes (ex. `.o`) rely on the map being complete
  let importTargets ← withReader (fun _ => cfg) do
    imports.filterMapM fun imp => OptionT.run do
      let mod := imp.module
      let pkg ← OptionT.mk <| getPackageForModule? mod
      recurse ⟨pkg, mod⟩
  let importSharedLibTargets := importTargets.filterMap (·.info.sharedLibTarget?)
  let importTarget ← ActiveTarget.collectOpaqueList <| importTargets.map (·.info.oleanTarget) ++ importSharedLibTargets
  let loadLibs := importSharedLibTargets.map (·.info)
  let precompiledPath := (← getWorkspace).packageList.map (·.libDir)
  let allDepsTarget := Target.active <| ← depTarget.mixOpaqueAsync importTarget
  -- TODO: it looks like `do match` ignores `generalizing`
  (match (generalizing := true) buildC, cfg.buildSharedLibs with
  | false, false => do
    let olean ← pkg.moduleOleanTargetOnly mod info.srcFile contents allDepsTarget |>.activate
    return olean.withInfo { mod, leanOutputTarget := olean }
  | true, false => do
    let oleanAndC ← pkg.moduleOleanAndCTargetOnly mod info.srcFile contents loadLibs.toArray precompiledPath allDepsTarget |>.activate
    return oleanAndC.withInfo { mod, leanOutputTarget := oleanAndC }
  | buildC, true => do
    let oleanAndC ← pkg.moduleOleanAndCTargetOnly mod info.srcFile contents loadLibs.toArray precompiledPath allDepsTarget |>.activate
    let oTarget ← leanOFileTarget (pkg.modToO mod) (Target.active oleanAndC.cTarget) pkg.moreLeancArgs
    let oTarget ← oTarget.activate
    let loadLibs := Std.RBTree.ofList <| loadLibs.map (·.toString)
    let moreLoadLibs :=
      if System.Platform.isWindows then
        -- we cannot have unresolved symbols on Windows, so we must pass the entire closure to the linker
        importTargets.foldl (Std.RBTree.union · ·.info.allLoadLibs) {} |>.diff loadLibs
      else
        -- on other platforms, it is sufficient to link against the direct dependencies,
        -- which when loaded will trigger loading the entire closure
        {}
    -- NOTE: we pass `moreLoadLibs` as direct arguments instead of targets,
    -- which is okay because they are the closure of `importSharedLibTargets`
    -- and so are already included in those traces
    let linkArgs := moreLoadLibs.toArray ++ pkg.moreLinkArgs
    let linkTargets := (oTarget :: importSharedLibTargets).toArray.map Target.active
    let sharedLibTarget ← leanSharedLibTarget (pkg.modToSharedLib mod) linkTargets linkArgs
    let sharedLibTarget ← sharedLibTarget.activate
    let allLoadLibs := moreLoadLibs.union loadLibs
    return sharedLibTarget.withInfo {
      leanOutputTarget := match (generalizing := true) buildC with
        | false => oleanAndC.oleanTarget
        | true  => oleanAndC
      sharedLibTarget? := sharedLibTarget
      mod, allLoadLibs })

-- ## Builders

/-- Build a single module using the recursive module build function `build`. -/
def buildModule (mod : ModuleInfo) (build : RecModuleBuild buildC) : BuildM (ActiveModuleTarget buildC) := do
  failOnBuildCycle <| ← ReaderT.run (r := {}) <| RBTopT.run' do
    buildRBTop (cmp := Name.quickCmp) build ModuleInfo.name mod

/--
Build each module using the recursive module function `build`,
constructing an `Array`  of the results.
-/
def buildModuleArray (mods : Array ModuleInfo)
(build : RecModuleBuild buildC) : BuildM (Array (ActiveModuleTarget buildC)) := do
  failOnBuildCycle <| ← ReaderT.run (r := {}) <| RBTopT.run' <| mods.mapM <|
    buildRBTop (cmp := Name.quickCmp) build ModuleInfo.name

/--
Build each module using the recursive module function `build`,
constructing a module-target `NameMap`  of the results.
-/
def buildModuleMap
(infos : Array ModuleInfo) (build : RecModuleBuild buildC)
: BuildM (NameMap (ActiveModuleTarget buildC)) := do
  let (x, objMap) ← ReaderT.run (r := {}) <| RBTopT.run do
    infos.forM fun info => discard <| buildRBTop build ModuleInfo.name info
  failOnBuildCycle x
  return objMap

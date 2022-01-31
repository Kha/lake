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

abbrev ModuleBuildM (α) :=
  -- equivalent to `RBTopT (cmp := Name.quickCmp) Name α BuildM`.
  -- phrased this way to use `NameMap`
  EStateT (List Name) (NameMap α) BuildM

abbrev RecModuleBuild (o) :=
  RecBuild ModuleInfo o (ModuleBuildM o)

abbrev RecModuleTargetBuild (i) :=
  RecModuleBuild (ActiveBuildTarget i)

/-
Produces a recursive module target builder that
builds the target module after recursively building its local imports
(relative to the workspace).
-/
def recBuildModuleWithLocalImports
(build : Package → Name → FilePath → String → List o → BuildM o)
: RecModuleBuild o := fun info recurse => do
  let contents ← IO.FS.readFile info.srcFile
  let (imports, _, _) ← Elab.parseImports contents info.srcFile.toString
  -- we construct the import targets even if a rebuild is not required
  -- because other build processes (ex. `.o`) rely on the map being complete
  let importTargets ← imports.filterMapM fun imp => OptionT.run do
    let mod := imp.module
    let pkg ← OptionT.mk <| getPackageForModule? mod
    recurse ⟨pkg, mod⟩
  build info.pkg info.name info.srcFile contents importTargets

structure ActivePrecompModuleTargets extends ActiveOleanAndCTargets where
  mod : Name
  sharedLibTarget : ActiveFileTarget
  -- NOTE: used only on Windows
  allLoadLibs : Std.RBTree String compare
deriving Inhabited

def recBuildModulePrecompTargetWithLocalImports (depTarget : ActiveBuildTarget x)
: RecModuleBuild (ActiveBuildTarget ActivePrecompModuleTargets) :=
  recBuildModuleWithLocalImports fun pkg mod leanFile contents importTargets => do
    let importSharedLibTargets := importTargets.map (·.info.sharedLibTarget)
    let importTarget ← ActiveTarget.collectOpaqueList <| importTargets.map (·.info.oleanTarget) ++ importSharedLibTargets
    let loadLibs := importSharedLibTargets.map (·.info)
    let precompiledPath := (← getWorkspace).packageList.map (·.libDir)
    let allDepsTarget := Target.active <| ← depTarget.mixOpaqueAsync importTarget
    let oleanAndC ← pkg.moduleOleanAndCTargetOnly mod leanFile contents loadLibs.toArray precompiledPath allDepsTarget
    let oleanAndC ← oleanAndC.activate
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
    return sharedLibTarget.withInfo { oleanAndC.info with mod, sharedLibTarget, allLoadLibs }

def recBuildModuleOleanAndCTargetWithLocalImports (depTarget : ActiveBuildTarget x)
: RecModuleBuild ActiveOleanAndCTarget :=
  recBuildModuleWithLocalImports fun pkg mod leanFile contents importTargets => do
    let importTarget ← ActiveTarget.collectOpaqueList <| importTargets.map (·.oleanTarget)
    let allDepsTarget := Target.active <| ← depTarget.mixOpaqueAsync importTarget
    pkg.moduleOleanAndCTargetOnly mod leanFile contents #[] [] allDepsTarget |>.activate

def recBuildModuleOleanTargetWithLocalImports (depTarget : ActiveBuildTarget x)
: RecModuleBuild ActiveFileTarget :=
  recBuildModuleWithLocalImports fun pkg mod leanFile contents importTargets => do
    let importTarget ← ActiveTarget.collectOpaqueList importTargets
    let allDepsTarget := Target.active <| ← depTarget.mixOpaqueAsync importTarget
    pkg.moduleOleanTargetOnly mod leanFile contents allDepsTarget |>.activate

-- ## Builders

/-- Build a single module using the recursive module build function `build`. -/
def buildModule (mod : ModuleInfo)
[Inhabited o] (build : RecModuleBuild o) : BuildM o := do
  failOnBuildCycle <| ← RBTopT.run' do
    buildRBTop (cmp := Name.quickCmp) build ModuleInfo.name mod

/--
Build each module using the recursive module function `build`,
constructing an `Array`  of the results.
-/
def buildModuleArray (mods : Array ModuleInfo)
[Inhabited o] (build : RecModuleBuild o) : BuildM (Array o) := do
  failOnBuildCycle <| ← RBTopT.run' <| mods.mapM <|
    buildRBTop (cmp := Name.quickCmp) build ModuleInfo.name

/--
Build each module using the recursive module function `build`,
constructing a module-target `NameMap`  of the results.
-/
def buildModuleMap [Inhabited o]
(infos : Array ModuleInfo) (build : RecModuleBuild o)
: BuildM (NameMap o) := do
  let (x, objMap) ← RBTopT.run do
    infos.forM fun info => discard <| buildRBTop build ModuleInfo.name info
  failOnBuildCycle x
  return objMap

/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Build.Monad

namespace Lake
open System

def createParentDirs (path : FilePath) : IO PUnit := do
  if let some dir := path.parent then IO.FS.createDirAll dir

def proc (args : IO.Process.SpawnArgs) : BuildM PUnit := do
  let envStr := String.join <| args.env.toList.map fun (k, v) => s!"{k}={v.getD ""} "
  let cmdStr := " ".intercalate (args.cmd :: args.args.toList)
  logInfo <| "> " ++ envStr ++
    match args.cwd with
    | some cwd => s!"{cmdStr}    # in directory {cwd}"
    | none     => cmdStr
  let out ← IO.Process.output args
  unless out.stdout.isEmpty do
    logInfo out.stdout
  unless out.stderr.isEmpty do
    logError out.stderr
  if out.exitCode != 0 then
    logError s!"external command {args.cmd} exited with status {out.exitCode}"
    failure

def compileOlean (leanFile oleanFile : FilePath)
(oleanPath : SearchPath := []) (rootDir : FilePath := ".")
(leanArgs : Array String := #[]) (lean : FilePath := "lean")
: BuildM PUnit := do
  createParentDirs oleanFile
  proc {
    cmd := lean.toString
    args := leanArgs ++ #[
      "-R", rootDir.toString, "-o", oleanFile.toString, leanFile.toString
    ]
    env := #[("LEAN_PATH", oleanPath.toString)]
  }

def compileOleanAndC (leanFile oleanFile cFile : FilePath)
(oleanPath : SearchPath := []) (rootDir : FilePath := ".")
(leanArgs : Array String := #[]) (lean : FilePath := "lean")
(precompiledPath : SearchPath := ∅)
: BuildM PUnit := do
  createParentDirs cFile
  createParentDirs oleanFile
  let mut env := #[("LEAN_PATH", some oleanPath.toString)]
  if !precompiledPath.isEmpty && System.Platform.isWindows then
    let path := (← IO.getEnv "PATH").getD ""
    -- set up search path for locating dependent DLLs
    env := env ++ #[("PATH", some (SearchPath.parse path ++ precompiledPath).toString)]
  proc {
    cmd := lean.toString
    args := leanArgs ++ #[
      "-R", rootDir.toString, "-o", oleanFile.toString, "-c",
      cFile.toString, leanFile.toString
    ]
    env
  }

def compileO (oFile srcFile : FilePath)
(moreArgs : Array String := #[]) (compiler : FilePath := "cc") : BuildM PUnit := do
  createParentDirs oFile
  proc {
    cmd := compiler.toString
    args := #["-c", "-o", oFile.toString, srcFile.toString] ++ moreArgs
  }

def compileStaticLib (libFile : FilePath)
(oFiles : Array FilePath) (ar : FilePath := "ar") : BuildM PUnit := do
  createParentDirs libFile
  proc {
    cmd := ar.toString
    args := #["rcs", libFile.toString] ++ oFiles.map toString
  }

def compileSharedLib (libFile : FilePath) (linkFiles : Array FilePath)
(linkArgs : Array String := #[]) (linker : FilePath := "cc") : BuildM PUnit := do
  createParentDirs libFile
  proc {
    cmd := linker.toString
    args := #["-shared", "-o", libFile.toString] ++ linkFiles.map toString ++ linkArgs
  }

def compileBin (binFile : FilePath) (linkFiles : Array FilePath)
(linkArgs : Array String := #[]) (linker : FilePath := "cc") : BuildM PUnit := do
  createParentDirs binFile
  proc {
    cmd := linker.toString
    args := #["-o", binFile.toString] ++ linkFiles.map toString ++ linkArgs
  }

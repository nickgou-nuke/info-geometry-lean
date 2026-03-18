import Lean
import Lean.Server.FileWorker

open Lean
open Lean.Server
open Lean.Server.FileWorker

private def moduleNameGuessFromFile (file : System.FilePath) : Option Name :=
  let parts := file.toString.splitOn "/"
  let relParts :=
    match parts.dropWhile (· != "lean") with
    | [] => parts
    | _ :: rest => rest
  match relParts.reverse with
  | [] => none
  | leafWithExt :: revRest =>
      if !leafWithExt.endsWith ".lean" then
        none
      else
        let leaf := (leafWithExt.dropEnd 5).toString
        let modParts := revRest.reverse ++ [leaf]
        some <| modParts.foldl (init := Name.anonymous) fun acc part =>
          if part.isEmpty then acc else Name.str acc part

private def openNullStream : IO IO.FS.Stream := do
  let h ← IO.FS.Handle.mk "/dev/null" IO.FS.Mode.write
  pure <| IO.FS.Stream.ofHandle h

private def mkDocumentMeta (file : System.FilePath) : IO DocumentMeta := do
  let realFile ← IO.FS.realPath file
  let text := (← IO.FS.readFile realFile).crlfToLf.toFileMap
  pure {
    uri := System.Uri.pathToUri realFile
    mod := moduleNameGuessFromFile realFile |>.getD `Main
    version := 0
    text := text
    dependencyBuildMode := .never
  }

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let inputFile := args.headD "lean/InfoGeometry/Canonical/GeneratedFlow.lean"
  let doc ← mkDocumentMeta inputFile
  let outStream ← openNullStream
  let errStream ← openNullStream
  let initParams : Lsp.InitializeParams := { capabilities := {} }
  let opts := Elab.async.setIfNotSet ({} : Options) false
  let (_, state) ← initializeWorker doc outStream errStream initParams opts
  let initSnap := state.doc.initSnap
  IO.println s!"headerParsedOk={initSnap.result?.isSome}"
  let (snapsList, err?) := state.doc.cmdSnaps.waitAll.get
  IO.println s!"cmdSnaps={snapsList.length}"
  IO.println s!"err?={err?.isSome}"
  pure 0

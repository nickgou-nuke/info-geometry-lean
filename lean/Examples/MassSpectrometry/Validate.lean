/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.MassSpectrometry.ValidatorIO

/-- Run with `lake env lean --run lean/Examples/MassSpectrometry/Validate.lean file.json`.
Exit 0 means structural acceptance, 1 rejection, 2 malformed input or usage. -/
def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match args with
  | [path] =>
    try
      let input ← IO.FS.readFile path
      match InfoGeometry.MassSpectrometry.ValidatorIO.checkJson input with
      | .ok true =>
        out.putStrLn "{\"structurallyAccepted\":true,\"arithmetic\":\"exact-rational\"}"
        return 0
      | .ok false =>
        out.putStrLn "{\"structurallyAccepted\":false,\"arithmetic\":\"exact-rational\"}"
        return 1
      | .error message =>
        err.putStrLn s!"invalid input: {message}"
        return 2
    catch e =>
      err.putStrLn s!"input error: {e}"
      return 2
  | _ =>
    err.putStrLn "usage: Validate.lean candidate.json"
    return 2

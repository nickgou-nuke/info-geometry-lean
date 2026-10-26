/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.MassSpectrometry.ValidatorIO

/-! Executable adversarial checks of the JSON boundary. -/
open Lean InfoGeometry.MassSpectrometry.ValidatorIO

private def expect (name input : String) (expected : String) : IO Unit := do
  let actual := match checkJson input with
    | .ok true => "accepted"
    | .ok false => "rejected"
    | .error _ => "malformed"
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {expected}, got {actual}")
  (← IO.getStdout).putStrLn s!"PASS {name}"

/-- Run with the checked-in two-fragment fixture as the sole argument. -/
def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: JsonChecks.lean fixture.json")
  let input ← IO.FS.readFile path
  let root ← match Json.parse input with
    | .ok (.obj fields) => pure (Json.obj fields)
    | _ => throw (IO.userError "fixture must be a JSON object")
  expect "two-condition chain" input "accepted"
  let cases : List (String × String × Json × String) := [
    ("cycle", "edge", toJson ([[false, true], [true, false]] : List (List Bool)), "rejected"),
    ("bad rank", "rank", toJson ([0, 1] : List Nat), "rejected"),
    ("mass increase", "fragmentMass", toJson (["60", "100"] : List String), "rejected"),
    ("negative intensity", "intensity", toJson (["1", "-1"] : List String), "rejected"),
    ("bad columns", "assignment", toJson ([["1", "0"], ["1", "0"]] : List (List String)),
      "rejected"),
    ("short vector", "peakMass", toJson (["100"] : List String), "malformed"),
    ("ragged matrix", "assignment", toJson ([["1"], ["0", "1"]] : List (List String)),
      "malformed"),
    ("short condition table", "weight", Json.arr #[], "malformed"),
    ("zero denominator", "intensity", toJson (["1", "1/0"] : List String), "malformed"),
    ("negative denominator", "intensity", toJson (["1", "1/-2"] : List String), "malformed"),
    ("float instead of rational string", "peakMass", toJson ([100, 60] : List Nat), "malformed")]
  for (name, key, value, expected) in cases do
    expect name (root.setObjVal! key value).compress expected
  expect "broken JSON" "{" "malformed"
  expect "missing fields" "{}" "malformed"
  return 0

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.MassSpectrometry.RationalCandidate
import Lean.Data.Json

/-!
# JSON input boundary for the rational validator

Rationals are strings `numerator/positive-denominator` (integers are also
accepted). Array dimensions are checked before constructing the finite input.
The soundness theorem applies to the parsed candidate; parsing and external
file provenance are not cryptographic proof certificates.
-/

namespace InfoGeometry.MassSpectrometry.ValidatorIO
open Lean

/-- Reject malformed fractions and zero denominators rather than using total
field division to turn a malformed input into a value. -/
def parseRational (s : String) : Except String ℚ := do
  match s.splitOn "/" with
  | [num] =>
    match num.toInt? with
    | some x => return (x : ℚ)
    | none => throw s!"invalid integer: {s}"
  | [num, den] =>
    match num.toInt?, den.toNat? with
    | some x, some y =>
      if y = 0 then throw "rational denominator must be positive"
      else return (x : ℚ) / (y : ℚ)
    | _, _ => throw s!"invalid rational: {s}"
  | _ => throw s!"invalid rational: {s}"

private def rational (j : Json) : Except String ℚ := do
  parseRational (← j.getStr?)

/-- A checked dimension gives bounded array indexing, without default padding. -/
private def vector {α : Type} (parse : Json → Except String α) (n : ℕ)
    (j : Json) : Except String (Fin n → α) := do
  let xs ← j.getArr?
  let ys ← xs.mapM parse
  if h : ys.size = n then
    return fun i => ys[i.val]'(by simp [h])
  else throw s!"expected vector length {n}, got {ys.size}"

private def matrix {α : Type} (parse : Json → Except String α) (n : ℕ)
    (j : Json) : Except String (Matrix (Fin n) (Fin n) α) :=
  vector (vector parse n) n j

/-- Parse each required field; every matrix and condition table is shape checked. -/
def parseCandidate (j : Json) : Except String (Σ n k, RationalCandidate n k) := do
  let n ← j.getObjValAs? Nat "n"
  let k ← j.getObjValAs? Nat "k"
  let peakMass ← vector rational n (← j.getObjVal? "peakMass")
  let intensity ← vector rational n (← j.getObjVal? "intensity")
  let edge ← matrix Json.getBool? n (← j.getObjVal? "edge")
  let rank ← vector Json.getNat? n (← j.getObjVal? "rank")
  let fragmentMass ← vector rational n (← j.getObjVal? "fragmentMass")
  let assignment ← matrix rational n (← j.getObjVal? "assignment")
  let weight ← vector (matrix rational n) k (← j.getObjVal? "weight")
  return ⟨n, k, { peakMass, intensity, edge, rank, fragmentMass, assignment, weight }⟩

/-- Pure input-to-decision entry point; parse errors remain separate from rejection. -/
def checkJson (input : String) : Except String Bool := do
  let j ← Json.parse input
  let ⟨_, _, c⟩ ← parseCandidate j
  return c.check

/-- JSON acceptance inherits the semantic model theorem for the parsed data. -/
theorem parsed_check_sound (input : String) (j : Json)
    {n k : ℕ} (c : RationalCandidate n k)
    (hj : Json.parse input = .ok j) (hc : parseCandidate j = .ok ⟨n, k, c⟩)
    (ha : checkJson input = .ok true) (select : CollisionCondition → Fin k) :
    ∃ h : c.Valid, IsStructurallyAdmissible (c.toModel h select) := by
  have hcheck : c.check = true := by
    unfold checkJson at ha
    rw [hj] at ha
    change (Except.map (fun x => x.2.2.check) (parseCandidate j)) = .ok true at ha
    rw [hc] at ha
    exact Except.ok.inj ha
  exact ⟨c.check_eq_true_iff.mp hcheck, c.check_sound hcheck select⟩

end InfoGeometry.MassSpectrometry.ValidatorIO

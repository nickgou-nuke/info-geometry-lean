/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection
import InfoGeometry.Canonical.DecomposableBivector
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Regression and trust audit for distinct-point Arnold coefficients

The repeated-index calculation records why the former scalar contract could
not admit nonzero field coefficients. Rational coordinates, a nonzero native
exterior blade, and noncommuting matrix residues exercise the repaired
construction. The final command audits the actual imported owners and the
named witness declarations; no analytic connection theorem is claimed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldKohnoDistinctPointsAudit

open ArnoldCohenBCFWBridge ArnoldKohnoParaKahlerConnection

/-- The old all-triples scalar hypothesis forces square-zero coefficients. -/
theorem total_partial_fraction_forces_square_zero
    {I R : Type*} [CommRing R] (c : I → I → R)
    (skew : ∀ i j, c j i = -c i j)
    (partial_fraction : ∀ i j k,
      c i j * c j k + c j k * c k i + c k i * c i j = 0)
    (i j : I) : c i j * c i j = 0 := by
  have h := partial_fraction i j i
  rw [skew i j, mul_neg, neg_mul] at h
  rw [mul_comm (c i i) (c i j), add_assoc,
      neg_add_cancel, add_zero] at h
  exact neg_eq_zero.mp h

/-- Over a field or domain the old hypothesis admits only zero coefficients. -/
theorem total_partial_fraction_forces_zero
    {I R : Type*} [CommRing R] [NoZeroDivisors R] (c : I → I → R)
    (skew : ∀ i j, c j i = -c i j)
    (partial_fraction : ∀ i j k,
      c i j * c j k + c j k * c k i + c k i * c i j = 0)
    (i j : I) : c i j = 0 :=
  mul_self_eq_zero.mp (total_partial_fraction_forces_square_zero c skew partial_fraction i j)

abbrev V := Fin 2 → ℚ

def e0 : V := (Pi.basisFun ℚ (Fin 2)) 0
def e1 : V := (Pi.basisFun ℚ (Fin 2)) 1

def points (n : ℕ) : ℚ := n

theorem points_injective : Function.Injective points := Nat.cast_injective

def differentials : ℕ → V
  | 0 => e0
  | 1 => 0
  | 2 => -e1
  | _ => 0

def data : LogarithmicOneFormData (R := ℚ) differentials :=
  LogarithmicOneFormData.reciprocalDifference differentials points points_injective

theorem coefficient_01 : data.c 0 1 = -1 := by
  norm_num [data, LogarithmicOneFormData.reciprocalDifference, points]

theorem coefficient_12 : data.c 1 2 = -1 := by
  norm_num [data, LogarithmicOneFormData.reciprocalDifference, points]

theorem coefficient_20 : data.c 2 0 = 1 / 2 := by
  norm_num [data, LogarithmicOneFormData.reciprocalDifference, points]

theorem coefficient_01_ne_zero : data.c 0 1 ≠ 0 := by
  rw [coefficient_01]
  norm_num

def a : ExteriorAlgebra ℚ V := data.exteriorForm differentials 0 1
def b : ExteriorAlgebra ℚ V := data.exteriorForm differentials 1 2
def c : ExteriorAlgebra ℚ V := data.exteriorForm differentials 2 0
def blade : ExteriorAlgebra ℚ V := ExteriorAlgebra.ι ℚ e0 * ExteriorAlgebra.ι ℚ e1

theorem a_eq : a = -ExteriorAlgebra.ι ℚ e0 := by
  simp [a, LogarithmicOneFormData.exteriorForm, LogarithmicOneFormData.form,
    coefficient_01, differentials]

theorem b_eq : b = -ExteriorAlgebra.ι ℚ e1 := by
  simp [b, LogarithmicOneFormData.exteriorForm, LogarithmicOneFormData.form,
    coefficient_12, differentials]

theorem c_eq : c = (-1 / 2 : ℚ) • (ExteriorAlgebra.ι ℚ e0 + ExteriorAlgebra.ι ℚ e1) := by
  simp only [c, LogarithmicOneFormData.exteriorForm, LogarithmicOneFormData.form,
    coefficient_20, differentials, map_smul, map_sub, map_neg]
  module

theorem blade_ne_zero : blade ≠ 0 := by
  have h := exteriorPower_ιMulti_ne_zero_of_linearIndependent
    (fun i : Fin 2 => (Pi.basisFun ℚ (Fin 2)) i)
    (Pi.basisFun ℚ (Fin 2)).linearIndependent
  intro hz
  apply h
  apply Subtype.ext
  simpa [blade, e0, e1, ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail] using hz

theorem first_channel : a * b = blade := by
  rw [a_eq, b_eq]
  simp [blade]

theorem first_channel_ne_zero : a * b ≠ 0 := by
  rw [first_channel]
  exact blade_ne_zero

theorem native_arnold_witness : a * b + b * c + c * a = 0 :=
  native_arnold_three_term_relation differentials data 0 1 2

theorem repeated_index_witness :
    data.exteriorForm differentials 0 1 * data.exteriorForm differentials 1 0 +
      data.exteriorForm differentials 1 0 * data.exteriorForm differentials 0 0 +
      data.exteriorForm differentials 0 0 * data.exteriorForm differentials 0 1 = 0 :=
  native_arnold_three_term_relation differentials data 0 1 0

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℚ

attribute [local instance 100] LieRing.ofAssociativeRing

def x : Mat2 := !![0, 1; 0, 0]
def y : Mat2 := !![0, 0; 1, 0]
def t : Mat2 := -x - y

theorem matrix_bracket : ⁅x, y⁆ = (!![1, 0; 0, -1] : Mat2) := by
  change x * y - y * x = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [x, y, Matrix.mul_apply, Fin.sum_univ_two]

theorem matrix_bracket_ne_zero : ⁅x, y⁆ ≠ 0 := by
  rw [matrix_bracket]
  intro h
  have h00 := congrArg (fun m : Mat2 => m 0 0) h
  norm_num at h00

theorem matrix_noncommuting : x * y ≠ y * x := by
  intro h
  apply matrix_bracket_ne_zero
  change x * y - y * x = 0
  rw [h, sub_self]

theorem matrix_kohno_first : ⁅x, t + y⁆ = 0 := by
  have ht : t + y = -x := by simp [t]
  rw [ht, lie_neg, lie_self, neg_zero]

theorem matrix_kohno_second : ⁅y, x + t⁆ = 0 := by
  have ht : x + t = -y := by simp [t, sub_eq_add_neg]
  rw [ht, lie_neg, lie_self, neg_zero]

/-- The constructed native forms cancel with genuinely noncommuting residues. -/
theorem matrix_kohno_triangle_witness : triangleCurvature x y t a b c = 0 :=
  reciprocalDifference_kohno_triangle_flat differentials points points_injective
    0 1 2 x y t matrix_kohno_first matrix_kohno_second

end InfoGeometry.Canonical.ArnoldKohnoDistinctPointsAudit

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners : Array Name := #[
    `InfoGeometry.Canonical.ArnoldCohenBCFWBridge,
    `InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection,
    `InfoGeometry.Canonical.DecomposableBivector,
    `InfoGeometry.Projective.AmplituhedronBostConnesSynthesis]
  let witnessPrefix := `InfoGeometry.Canonical.ArnoldKohnoDistinctPointsAudit
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for owner in owners do
    unless modules.contains owner do
      throwError "ARNOLD_KOHNO_AUDIT_FAILURE: missing owner {owner}"
  let mut count : Nat := 0
  let mut counts : NameMap Nat := {}
  let mut used : Array Name := #[]
  for (name, info) in env.constants do
    let owner := match env.getModuleIdxFor? name with
      | some idx => modules[idx.toNat]!
      | none => witnessPrefix
    if !owners.contains owner && !witnessPrefix.isPrefixOf name then continue
    if let .axiomInfo _ := info then
      throwError "ARNOLD_KOHNO_AUDIT_FAILURE: introduced axiom {name}"
    if info.isUnsafe || info.isPartial then
      throwError "ARNOLD_KOHNO_AUDIT_FAILURE: unsafe or partial declaration {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "ARNOLD_KOHNO_AUDIT_FAILURE: {name} depends on {ax}"
      if !used.contains ax then used := used.push ax
    count := count + 1
    counts := counts.insert owner ((counts.find? owner).getD 0 + 1)
  for owner in owners.push witnessPrefix do
    let n := (counts.find? owner).getD 0
    if n == 0 then throwError "ARNOLD_KOHNO_AUDIT_FAILURE: empty owner {owner}"
    logInfo m!"ARNOLD_KOHNO_AUDIT_OWNER: {owner}: {n}"
  logInfo m!"ARNOLD_KOHNO_AUDIT_AXIOMS: {used.qsort Name.lt}"
  logInfo m!"ARNOLD_KOHNO_AUDIT_SUCCESS: {count} declarations"

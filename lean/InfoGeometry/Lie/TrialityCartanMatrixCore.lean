/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The existing four-dimensional Cartan triality matrix core

This module relocates the Hadamard/reflection presentation and its common
fixed submodule from the larger Krein/Clifford/G₂ synthesis. The declaration
names, statements, proof bodies, and original namespace are retained.
The last-coordinate reflection is the convention of this owner.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis

open BigOperators Matrix

section CartanS3Triality

/-- Vector–Spinor Hadamard swap `σ_{VS} = ½ H₄` on `ℝ⁴`. -/
def trialitySwapVS : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

/-- Spinor chirality reflection `σ_{±} = diag(1, 1, 1, -1)` on `ℝ⁴`. -/
def trialitySwapSpin : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- Order-3 Cartan triality cycle `τ = σ_{VS} σ_{±}` on `ℝ⁴`. -/
def trialityCycle3 : Matrix (Fin 4) (Fin 4) ℝ :=
  trialitySwapVS * trialitySwapSpin

/-- Exact `S₃` Coxeter/Weyl presentation of Cartan triality on `ℝ⁴`:
`σ_{VS}² = 1`, `σ_{±}² = 1`, `τ³ = 1`, `τ ≠ 1`, and `σ_{±} τ σ_{±} = τ²`. -/
theorem cartan_s3_triality_presentation :
    trialitySwapVS * trialitySwapVS = 1 ∧
    trialitySwapSpin * trialitySwapSpin = 1 ∧
    trialityCycle3 ^ 3 = 1 ∧
    trialityCycle3 ≠ 1 ∧
    trialitySwapSpin * trialityCycle3 * trialitySwapSpin = trialityCycle3 ^ 2 := by
  have hvs : trialitySwapVS * trialitySwapVS = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trialitySwapVS, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  have hsp : trialitySwapSpin * trialitySwapSpin = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trialitySwapSpin, Matrix.mul_apply, Fin.sum_univ_four]
  have htau3 : trialityCycle3 ^ 3 = 1 := by
    unfold trialityCycle3
    rw [pow_three]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trialitySwapVS, trialitySwapSpin, Matrix.mul_apply,
        Fin.sum_univ_four] <;> norm_num
  have hne : trialityCycle3 ≠ 1 := by
    intro h
    have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
    unfold trialityCycle3 trialitySwapVS trialitySwapSpin at h00
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00
    norm_num at h00
  have hconj : trialitySwapSpin * trialityCycle3 * trialitySwapSpin = trialityCycle3 ^ 2 := by
    unfold trialityCycle3
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [trialitySwapVS, trialitySwapSpin, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  exact ⟨hvs, hsp, htau3, hne, hconj⟩

/-- Explicit OpenGauss `T16` non-commutativity witness on `Matrix (Fin 4) (Fin 4) ℝ`. -/
theorem triality_mat4_noncommutative :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨trialitySwapVS, trialitySwapSpin, ?_⟩
  intro h
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 3) h
  unfold trialitySwapVS trialitySwapSpin at h03
  simp only [Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at h03
  norm_num at h03

/-- Explicit `S₃`-fixed Cartan submodule of `Fin 4 → ℝ` under `trialitySwapVS` and `trialitySwapSpin`. -/
def s3FixedCartanSubmodule : Submodule ℝ (Fin 4 → ℝ) where
  carrier := {v | trialitySwapVS.mulVec v = v ∧ trialitySwapSpin.mulVec v = v}
  zero_mem' := ⟨Matrix.mulVec_zero _, Matrix.mulVec_zero _⟩
  add_mem' {u v} hu hv :=
    ⟨by rw [Matrix.mulVec_add, hu.1, hv.1], by rw [Matrix.mulVec_add, hu.2, hv.2]⟩
  smul_mem' r v hv :=
    ⟨by rw [Matrix.mulVec_smul, hv.1], by rw [Matrix.mulVec_smul, hv.2]⟩

/-- Characterization of the `S₃`-fixed Cartan locus: `(v 3 = 0 ∧ v 0 = v 1 + v 2)`. -/
theorem cartan_s3_fixed_subspace_iff (v : Fin 4 → ℝ) :
    v ∈ s3FixedCartanSubmodule ↔ (v 3 = 0 ∧ v 0 = v 1 + v 2) := by
  change (trialitySwapVS.mulVec v = v ∧ trialitySwapSpin.mulVec v = v) ↔ (v 3 = 0 ∧ v 0 = v 1 + v 2)
  constructor
  · rintro ⟨hvs, hsp⟩
    have h3 : (trialitySwapSpin.mulVec v) 3 = v 3 := congrFun hsp 3
    have h0 : (trialitySwapVS.mulVec v) 0 = v 0 := congrFun hvs 0
    simp only [trialitySwapSpin, trialitySwapVS, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Matrix.of_apply] at h3 h0
    norm_num at h3 h0
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hv3, hv0⟩
    constructor
    · ext i
      fin_cases i <;>
        simp [trialitySwapVS, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv3, hv0] <;>
        linarith
    · ext i
      fin_cases i <;>
        simp [trialitySwapSpin, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv3]

/-- Explicit `ℝ`-linear equivalence `(Fin 2 → ℝ) ≃ₗ[ℝ] s3FixedCartanSubmodule`. -/
def s3FixedCartanEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] s3FixedCartanSubmodule where
  toFun p := ⟨![p 0 + p 1, p 0, p 1, 0],
    (cartan_s3_fixed_subspace_iff _).mpr ⟨rfl, rfl⟩⟩
  invFun v := ![v.1 1, v.1 2]
  left_inv p := by
    ext i
    fin_cases i <;> simp
  right_inv v := by
    apply Subtype.ext
    have hv := (cartan_s3_fixed_subspace_iff v.1).mp v.2
    ext i
    fin_cases i <;> simp [hv.1, hv.2]
  map_add' p q := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' r p := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [mul_add]

/-- The `S₃` triality symmetry cuts the 4D `D₄` Cartan subalgebra down to exact dimension `2`. -/
theorem finrank_s3FixedCartanSubmodule :
    Module.finrank ℝ s3FixedCartanSubmodule = 2 := by
  have h := s3FixedCartanEquiv.finrank_eq
  rw [Module.finrank_fin_fun] at h
  exact h.symm

end CartanS3Triality

end InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis

end

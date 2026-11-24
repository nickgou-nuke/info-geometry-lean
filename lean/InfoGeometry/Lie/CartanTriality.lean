/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

/-!
# Two coordinates for the four-dimensional Cartan triality representation

The elementary Cartan declarations retain their original namespace and names
from `KreinCl44SplitG2DerivationPosetSynthesis`; their extraction lets algebraic
consumers use the exact same owners without importing the Clifford and G₂
construction. The additional first-coordinate reflection is conjugate to the
existing fourth-coordinate reflection by an explicit orthogonal involution.

All form identities below concern the standard real dot product on `Fin 4 → ℝ`.
A Lie-algebra Killing-form identification requires its own explicit map.
-/

set_option autoImplicit false
noncomputable section
open BigOperators Matrix

namespace InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis

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

end InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis

namespace InfoGeometry.Lie.CartanTriality

open InfoGeometry.Lie.KreinCl44SplitG2DerivationPosetSynthesis

/-- Reflection in the first coordinate. -/
def conjugationReflection : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The Hadamard/first-coordinate-reflection cycle. -/
def cyclicTriality : Matrix (Fin 4) (Fin 4) ℝ :=
  trialitySwapVS * conjugationReflection

/-- The signed coordinate interchange `(v₀,v₁,v₂,v₃) ↦ (-v₃,v₁,v₂,-v₀)`. -/
def coordinateChange : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, -1; 0, 1, 0, 0; 0, 0, 1, 0; -1, 0, 0, 0]

theorem coordinateChange_sq : coordinateChange * coordinateChange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateChange, Matrix.mul_apply, Fin.sum_univ_four]

theorem coordinateChange_orthogonal : coordinateChangeᵀ * coordinateChange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateChange, Matrix.mul_apply, Fin.sum_univ_four]

theorem coordinateChange_mulVec (v : Fin 4 → ℝ) :
    coordinateChange.mulVec v = ![-v 3, v 1, v 2, -v 0] := by
  ext i
  fin_cases i <;> simp [coordinateChange, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The Hadamard generator is unchanged by the coordinate conversion. -/
theorem coordinateChange_conj_hadamard :
    coordinateChange * trialitySwapVS * coordinateChange = trialitySwapVS := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateChange, trialitySwapVS, Matrix.mul_apply, Fin.sum_univ_four]

/-- The old chirality reflection is transported to the supplied first-coordinate reflection. -/
theorem coordinateChange_conj_reflection :
    coordinateChange * trialitySwapSpin * coordinateChange = conjugationReflection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateChange, trialitySwapSpin, conjugationReflection,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- The order-three generators are related by the same coordinate conversion. -/
theorem coordinateChange_conj_cycle :
    coordinateChange * trialityCycle3 * coordinateChange = cyclicTriality := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateChange, trialityCycle3, cyclicTriality, trialitySwapVS,
      trialitySwapSpin, conjugationReflection, Matrix.mul_apply, Fin.sum_univ_four]

theorem conjugationReflection_sq : conjugationReflection * conjugationReflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conjugationReflection, Matrix.mul_apply, Fin.sum_univ_four]

theorem cyclicTriality_cube : cyclicTriality ^ 3 = 1 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicTriality, trialitySwapVS, conjugationReflection,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem cyclicTriality_ne_one : cyclicTriality ≠ 1 := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
  norm_num [cyclicTriality, trialitySwapVS, conjugationReflection,
    Matrix.mul_apply, Fin.sum_univ_four] at he

theorem cyclicTriality_sq_ne_one : cyclicTriality ^ 2 ≠ 1 := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
  norm_num [pow_two, cyclicTriality, trialitySwapVS, conjugationReflection,
    Matrix.mul_apply, Fin.sum_univ_four] at he

theorem cyclicTriality_order : orderOf cyclicTriality = 3 := by
  apply orderOf_eq_prime
  · exact cyclicTriality_cube
  · exact cyclicTriality_ne_one

/-- The reflection conjugates the cycle to its inverse (its square). -/
theorem reflection_conj_cycle :
    conjugationReflection * cyclicTriality * conjugationReflection = cyclicTriality ^ 2 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicTriality, trialitySwapVS, conjugationReflection,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- A concrete noncommutativity witness on the full matrix carrier. -/
theorem hadamard_reflection_noncommutative :
    trialitySwapVS * conjugationReflection ≠ conjugationReflection * trialitySwapVS := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
  norm_num [trialitySwapVS, conjugationReflection,
    Matrix.mul_apply, Fin.sum_univ_four] at he

theorem hadamard_orthogonal : trialitySwapVSᵀ * trialitySwapVS = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [trialitySwapVS, Matrix.mul_apply, Fin.sum_univ_four]

theorem reflection_orthogonal : conjugationReflectionᵀ * conjugationReflection = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conjugationReflection, Matrix.mul_apply, Fin.sum_univ_four]

theorem cycle_orthogonal : cyclicTrialityᵀ * cyclicTriality = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicTriality, trialitySwapVS, conjugationReflection,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Common fixed vectors of the two requested generators, as a native submodule. -/
def fixedCartan : Submodule ℝ (Fin 4 → ℝ) where
  carrier := {v | trialitySwapVS.mulVec v = v ∧ conjugationReflection.mulVec v = v}
  zero_mem' := ⟨Matrix.mulVec_zero _, Matrix.mulVec_zero _⟩
  add_mem' {u v} hu hv :=
    ⟨by rw [Matrix.mulVec_add, hu.1, hv.1], by rw [Matrix.mulVec_add, hu.2, hv.2]⟩
  smul_mem' r v hv :=
    ⟨by rw [Matrix.mulVec_smul, hv.1], by rw [Matrix.mulVec_smul, hv.2]⟩

theorem mem_fixedCartan_iff (v : Fin 4 → ℝ) :
    v ∈ fixedCartan ↔ v 0 = 0 ∧ v 1 + v 2 + v 3 = 0 := by
  change (trialitySwapVS.mulVec v = v ∧ conjugationReflection.mulVec v = v) ↔ _
  constructor
  · rintro ⟨hH, hS⟩
    have h0 := congrFun hS 0
    have hsum := congrFun hH 0
    simp [conjugationReflection, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0
    simp [trialitySwapVS, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hsum
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h0, hsum⟩
    constructor
    · ext i
      fin_cases i <;>
        simp [trialitySwapVS, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> linarith
    · ext i
      fin_cases i <;>
        simp [conjugationReflection, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h0]

/-- Explicit two-coordinate parametrization of the common fixed plane. -/
def fixedCartanEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] fixedCartan where
  toFun p := ⟨![0, p 0, p 1, -(p 0 + p 1)],
    (mem_fixedCartan_iff _).mpr ⟨rfl, by simp⟩⟩
  invFun v := ![v.1 1, v.1 2]
  left_inv p := by
    ext i
    fin_cases i <;> simp
  right_inv v := by
    apply Subtype.ext
    have hv := (mem_fixedCartan_iff v.1).mp v.2
    ext i
    fin_cases i
    · change 0 = v.1 0
      exact hv.1.symm
    · rfl
    · rfl
    · change -(v.1 1 + v.1 2) = v.1 3
      linarith [hv.2]
  map_add' p q := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp
    · simp
    · simp
    · simp
      ring
  map_smul' r p := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [mul_add]

theorem finrank_fixedCartan : Module.finrank ℝ fixedCartan = 2 := by
  have h := fixedCartanEquiv.finrank_eq
  rw [Module.finrank_fin_fun] at h
  exact h.symm

/-- A native basis of the fixed plane, obtained from its explicit parametrization. -/
def fixedCartanBasis : Module.Basis (Fin 2) ℝ fixedCartan :=
  (Pi.basisFun ℝ (Fin 2)).map fixedCartanEquiv

theorem fixedCartanBasis_zero :
    (fixedCartanBasis 0 : Fin 4 → ℝ) = ![0, 1, 0, -1] := by
  ext i
  fin_cases i <;> simp [fixedCartanBasis, fixedCartanEquiv, Pi.basisFun_apply]

theorem fixedCartanBasis_one :
    (fixedCartanBasis 1 : Fin 4 → ℝ) = ![0, 0, 1, -1] := by
  ext i
  fin_cases i <;> simp [fixedCartanBasis, fixedCartanEquiv, Pi.basisFun_apply]

/-- Membership is transported between the original and first-coordinate fixed planes. -/
theorem coordinateChange_mem_fixedCartan_iff (v : Fin 4 → ℝ) :
    coordinateChange.mulVec v ∈ fixedCartan ↔ v ∈ s3FixedCartanSubmodule := by
  rw [mem_fixedCartan_iff, cartan_s3_fixed_subspace_iff, coordinateChange_mulVec]
  change (-v 3 = 0 ∧ v 1 + v 2 + -v 0 = 0) ↔
    (v 3 = 0 ∧ v 0 = v 1 + v 2)
  constructor
  · rintro ⟨h0, hsum⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h3, hsum⟩
    constructor <;> linarith

/-- First vertex of the explicit three-element weight orbit. -/
def vectorWeight : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- Second vertex of the explicit three-element weight orbit. -/
def spinorWeightMinus : Fin 4 → ℝ := ![-(1 / 2), -(1 / 2), -(1 / 2), -(1 / 2)]

/-- Third vertex of the explicit three-element weight orbit. -/
def spinorWeightPlus : Fin 4 → ℝ := ![-(1 / 2), 1 / 2, 1 / 2, 1 / 2]

theorem cycle_vectorWeight : cyclicTriality.mulVec vectorWeight = spinorWeightMinus := by
  ext i
  fin_cases i <;> norm_num [cyclicTriality, trialitySwapVS, conjugationReflection,
    vectorWeight, spinorWeightMinus, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]

theorem cycle_spinorWeightMinus :
    cyclicTriality.mulVec spinorWeightMinus = spinorWeightPlus := by
  ext i
  fin_cases i <;> norm_num [cyclicTriality, trialitySwapVS, conjugationReflection,
    spinorWeightMinus, spinorWeightPlus, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]

theorem cycle_spinorWeightPlus : cyclicTriality.mulVec spinorWeightPlus = vectorWeight := by
  ext i
  fin_cases i <;> norm_num [cyclicTriality, trialitySwapVS, conjugationReflection,
    spinorWeightPlus, vectorWeight, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]

theorem weight_orbit_distinct : vectorWeight ≠ spinorWeightMinus ∧
    vectorWeight ≠ spinorWeightPlus ∧ spinorWeightMinus ≠ spinorWeightPlus := by
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num [vectorWeight, spinorWeightMinus] at h0
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num [vectorWeight, spinorWeightPlus] at h0
  · intro h
    have h1 := congrFun h 1
    norm_num [spinorWeightMinus, spinorWeightPlus] at h1

/-- All three orbit vectors have unit standard Euclidean norm squared. -/
theorem weight_orbit_norm_sq :
    dotProduct vectorWeight vectorWeight = 1 ∧
    dotProduct spinorWeightMinus spinorWeightMinus = 1 ∧
    dotProduct spinorWeightPlus spinorWeightPlus = 1 := by
  norm_num [vectorWeight, spinorWeightMinus, spinorWeightPlus, dotProduct, Fin.sum_univ_four]

end InfoGeometry.Lie.CartanTriality

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.MatrixCommutatorHodge
import InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel
import InfoGeometry.Quantum.BoundaryInstrument
import Mathlib.Data.Matrix.Basis

/-!
# Universal fixed effects of finite matrix Kraus families

A complete matrix-unit reset family proves that an effect fixed by every
complete finite Kraus family is scalar. This is a universal-family result;
a single family, or a single input state, does not imply centrality.
The explicit two-dimensional example has positive normalized state, positive
bounded effect, and a complete unitary family, while its nonzero operator
defect has zero expectation in that state.
-/

noncomputable section

namespace InfoGeometry.Quantum.Choi

open Matrix
open scoped ComplexOrder MatrixOrder
open InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel

universe u
variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The generic backward Kraus action agrees with the existing matrix Kraus
map evaluated at the adjointed family. -/
theorem krausDual_eq_krausMap_star {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) (E : Matrix n n ℂ) :
    krausDual V E = krausMap (fun i => star (V i)) E := by
  simp only [krausDual, krausMap, LinearMap.coe_mk, AddHom.coe_mk, star_star]

/-- The reset family sends each input basis vector to the chosen output
basis vector `r`. Its members are full matrix operators. -/
def resetKraus (r : n) (i : n) : Matrix n n ℂ := Matrix.single r i 1

omit [Fintype n] in
@[simp] theorem star_resetKraus (r i : n) :
    star (resetKraus r i) = Matrix.single i r 1 := by
  change (Matrix.single r i (1 : ℂ))ᴴ = _
  simp

/-- The matrix-unit reset family is complete in the trace-preserving order. -/
theorem resetKraus_complete (r : n) :
    ∑ i, star (resetKraus r i) * resetKraus r i = 1 := by
  simp only [star_resetKraus]
  simp only [resetKraus, Matrix.single_mul_single_same, one_mul]
  exact Matrix.sum_single_one

/-- Resetting to a basis state pulls every observable back to its diagonal
expectation times the identity. -/
theorem krausMap_star_resetKraus (r : n) (E : Matrix n n ℂ) :
    krausMap (fun i => star (resetKraus r i)) E = Matrix.scalar n (E r r) := by
  simp only [krausMap, LinearMap.coe_mk, AddHom.coe_mk, star_star]
  simp only [star_resetKraus]
  simp only [resetKraus, Matrix.single_mul_mul_single, one_mul, mul_one]
  exact Matrix.sum_single_eq_diagonal _

/-- A reset family acts on arbitrary matrices by trace times its output
rank-one projector, exhibiting the actual replacement channel formula. -/
theorem krausMap_resetKraus (r : n) (X : Matrix n n ℂ) :
    krausMap (resetKraus r) X = Matrix.trace X • Matrix.single r r 1 := by
  simp only [krausMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [star_resetKraus]
  simp only [resetKraus, Matrix.single_mul_mul_single, one_mul, mul_one]
  ext a b
  simp [Matrix.sum_apply, Matrix.single, Matrix.trace, Matrix.diag,
    Finset.sum_ite_irrel]

/-- Fixing every complete family of the matrix-index cardinality is already
enough to force a scalar observable; the reset family supplies the witness. -/
theorem fixed_by_all_indexed_kraus_iff_scalar [Nonempty n] (E : Matrix n n ℂ) :
    (∀ V : n → Matrix n n ℂ,
      (∑ i, star (V i) * V i) = 1 →
      krausMap (fun i => star (V i)) E = E) ↔
      ∃ c : ℂ, E = Matrix.scalar n c := by
  constructor
  · intro h
    let r : n := Classical.choice inferInstance
    refine ⟨E r r, ?_⟩
    have hr := h (resetKraus r) (resetKraus_complete r)
    rw [krausMap_star_resetKraus] at hr
    exact hr.symm
  · rintro ⟨c, rfl⟩ V hV
    rw [← krausDual_eq_krausMap_star]
    exact krausDual_eq_self_of_commute V (Matrix.scalar n c) hV
      (fun i => Matrix.scalar_commute c (fun z => mul_comm c z) (V i))

/-- Quantifying over all finite complete families gives precisely the scalar
effects on a nonempty full complex matrix algebra. -/
theorem fixed_by_all_kraus_iff_scalar [Nonempty n] (E : Matrix n n ℂ) :
    (∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (V : ι → Matrix n n ℂ),
      (∑ i, star (V i) * V i) = 1 →
      krausMap (fun i => star (V i)) E = E) ↔
      ∃ c : ℂ, E = Matrix.scalar n c := by
  constructor
  · intro h
    exact (fixed_by_all_indexed_kraus_iff_scalar E).mp (h n)
  · rintro ⟨c, rfl⟩ ι _ _ V hV
    rw [← krausDual_eq_krausMap_star]
    exact krausDual_eq_self_of_commute V (Matrix.scalar n c) hV
      (fun i => Matrix.scalar_commute c (fun z => mul_comm c z) (V i))

/-- The universal-family conclusion is exactly membership in the native
matrix-algebra center, using Mathlib's center classification. -/
theorem fixed_by_all_kraus_iff_mem_center [Nonempty n] (E : Matrix n n ℂ) :
    (∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (V : ι → Matrix n n ℂ),
      (∑ i, star (V i) * V i) = 1 →
      krausMap (fun i => star (V i)) E = E) ↔
      E ∈ Set.center (Matrix n n ℂ) := by
  rw [fixed_by_all_kraus_iff_scalar, Matrix.center_eq_range]
  exact exists_congr fun c => eq_comm

/-- For a frame generating the full matrix algebra, universal invariance
under complete finite Kraus families is exactly degree-zero harmonicity. -/
theorem fixed_by_all_kraus_iff_laplacian_eq_zero [Nonempty n]
    {ι : Type*} [Fintype ι] (Q : ι → Matrix n n ℂ)
    (hQ : Algebra.adjoin ℂ (Set.range Q) = ⊤) (E : Matrix n n ℂ) :
    (∀ (κ : Type u) [Fintype κ] [DecidableEq κ] (V : κ → Matrix n n ℂ),
      (∑ i, star (V i) * V i) = 1 →
      krausMap (fun i => star (V i)) E = E) ↔
      ((InfoGeometry.OperatorAlgebra.MatrixCommutatorHodge.codifferential Q).comp
        (InfoGeometry.OperatorAlgebra.MatrixCommutatorHodge.differential Q)) E = 0 := by
  rw [fixed_by_all_kraus_iff_mem_center]
  change E ∈ (Subalgebra.center ℂ (Matrix n n ℂ)).toSubmodule ↔
    E ∈ ((InfoGeometry.OperatorAlgebra.MatrixCommutatorHodge.codifferential Q).comp
      (InfoGeometry.OperatorAlgebra.MatrixCommutatorHodge.differential Q)).ker
  rw [InfoGeometry.OperatorAlgebra.MatrixCommutatorHodge.ker_laplacian_eq_center Q hQ]

end InfoGeometry.Quantum.Choi

namespace InfoGeometry.Quantum.BoundaryInstrument

open Matrix InfoGeometry.Algebra.FiniteSpin
open scoped ComplexOrder MatrixOrder

/-- Noncommutation and a nonzero backward operator defect can coexist with
zero scalar disturbance in a normalized positive state. The witness is the
maximally mixed state, the first basis effect, and the Pauli flip assembled
from the existing finite-spin raising and lowering operators. -/
theorem exists_noncommuting_zero_scalar_anomaly :
    ∃ (ρ E U : Mat2C),
      ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      E.PosSemidef ∧ (1 - E).PosSemidef ∧
      star U * U = 1 ∧
      E * U ≠ U * E ∧
      Choi.krausMap (fun _ : Unit => star U) E - E ≠ 0 ∧
      Matrix.trace (ρ * (Choi.krausMap (fun _ : Unit => star U) E - E)) = 0 := by
  let ρ : Mat2C := (1 / 2 : ℂ) • 1
  let E : Mat2C := Matrix.single 0 0 1
  let U : Mat2C := J_plus + J_minus
  have hρ : ρ.PosSemidef := Matrix.PosSemidef.one.smul
    (by norm_num [Complex.nonneg_iff] : 0 ≤ (1 / 2 : ℂ))
  have htr : Matrix.trace ρ = 1 := by
    norm_num [ρ, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hE : E.PosSemidef := by
    have hgram : E * Eᴴ = E := by
      simp [E, Matrix.single_mul_single_same]
    rw [← hgram]
    exact Matrix.posSemidef_self_mul_conjTranspose E
  have hEc : (1 - E).PosSemidef := by
    have hEq : (1 : Mat2C) - E = Matrix.single 1 1 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [E, Matrix.single]
    rw [hEq]
    have hgram :
        (Matrix.single 1 1 (1 : ℂ) : Mat2C) * (Matrix.single 1 1 (1 : ℂ))ᴴ =
          Matrix.single 1 1 (1 : ℂ) := by simp
    rw [← hgram]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hU : star U * U = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U, J_plus, J_minus, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two]
  have hcomm : E * U ≠ U * E := by
    intro h
    have h01 := congrArg (fun M : Mat2C => M 0 1) h
    norm_num [E, U, J_plus, J_minus, Matrix.mul_apply, Matrix.single,
      Fin.sum_univ_two] at h01
  have hdef : Choi.krausMap (fun _ : Unit => star U) E - E ≠ 0 := by
    intro h
    have h00 := congrArg (fun M : Mat2C => M 0 0) h
    norm_num [Choi.krausMap, E, U, J_plus, J_minus, Matrix.mul_apply,
      Matrix.star_apply, Matrix.single, Fin.sum_univ_two] at h00
  refine ⟨ρ, E, U, hρ, htr, hE, hEc, hU, hcomm, hdef, ?_⟩
  norm_num [Choi.krausMap, ρ, E, U, J_plus, J_minus, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Matrix.single, Fin.sum_univ_two]

end InfoGeometry.Quantum.BoundaryInstrument

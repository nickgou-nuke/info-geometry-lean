/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GrowingOnsiteMatrixHamiltonian
import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Native C⋆-matrix bounds for the growing onsite Hamiltonians

The finite recursion is transported through Mathlib's existing CStarMatrix
star equivalence. The fresh tilt is a self-adjoint unitary of norm one, and
the native successor map is contractive. Absolute summability of the actual
weights yields a derived uniform bound, not a bound supplied as a field.
The onsite owner import is a pending promotion dependency of this candidate.
-/
noncomputable section
open scoped ComplexOrder

namespace InfoGeometry.Canonical.GrowingOnsiteMatrixNorm

open CuntzMatrixTowerInstantiation CuntzMatrixTraceTower
open CantorBernoulliCStarMatrixTraceState GrowingOnsiteMatrixHamiltonian
open InfoGeometry.Physics.KleinBottleSewingExact

/-- The already constructed raw tail in Mathlib's native operator-norm carrier. -/
def cstarTailZ (n : ℕ) : CStarMatrixStage (n + 1) :=
  CStarMatrix.ofMatrixStarAlgEquiv (tailZ n)

/-- The same onsite Hamiltonian, not a replacement recursion or carrier. -/
def cstarOnsiteHamiltonian (w : ℕ → ℝ) (n : ℕ) : CStarMatrixStage n :=
  CStarMatrix.ofMatrixStarAlgEquiv (onsiteHamiltonian w n)

theorem cstarTailZ_selfAdjoint (n : ℕ) : IsSelfAdjoint (cstarTailZ n) := by
  change star (CStarMatrix.ofMatrixStarAlgEquiv (tailZ n) : CStarMatrixStage (n + 1)) = _
  rw [← map_star]
  exact congrArg (CStarMatrix.ofMatrixStarAlgEquiv :
    MatrixStage (n + 1) ≃⋆ₐ[ℂ] CStarMatrixStage (n + 1)) (tailZ_isHermitian n)

theorem cstarTailZ_sq (n : ℕ) : cstarTailZ n * cstarTailZ n = 1 := by
  have hz : tailZ n * tailZ n = 1 := by
    change tailEmbedding n tilt2 * tailEmbedding n tilt2 = 1
    rw [← map_mul, tilt2_sq, map_one]
  change CStarMatrix.ofMatrixStarAlgEquiv (tailZ n) *
    CStarMatrix.ofMatrixStarAlgEquiv (tailZ n) = (1 : CStarMatrixStage (n + 1))
  rw [← map_mul, hz, map_one]

theorem cstarTailZ_mem_unitary (n : ℕ) : cstarTailZ n ∈ unitary (CStarMatrixStage (n + 1)) := by
  constructor <;> rw [(cstarTailZ_selfAdjoint n).star_eq, cstarTailZ_sq]

theorem cstarTailZ_norm (n : ℕ) : ‖cstarTailZ n‖ = 1 :=
  CStarRing.norm_of_mem_unitary (cstarTailZ_mem_unitary n)

/-- Contractivity is native C⋆ star-hom contractivity, not a raw matrix norm claim. -/
theorem cstarConcreteStep_norm_le (n : ℕ) (A : CStarMatrixStage n) :
    ‖cstarConcreteStep n A‖ ≤ ‖A‖ :=
  NonUnitalStarAlgHom.norm_apply_le (cstarConcreteStep n) A

@[simp] theorem cstarOnsiteHamiltonian_zero (w : ℕ → ℝ) :
    cstarOnsiteHamiltonian w 0 = 0 := rfl

/-- Exact transport of the original real-weighted recursion. -/
theorem cstarOnsiteHamiltonian_succ (w : ℕ → ℝ) (n : ℕ) :
    cstarOnsiteHamiltonian w (n + 1) =
      cstarConcreteStep n (cstarOnsiteHamiltonian w n) + w n • cstarTailZ n := rfl

theorem cstarOnsiteHamiltonian_norm_le_sum (w : ℕ → ℝ) (n : ℕ) :
    ‖cstarOnsiteHamiltonian w n‖ ≤ ∑ j ∈ Finset.range n, |w j| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cstarOnsiteHamiltonian_succ, Finset.sum_range_succ]
    calc
      ‖cstarConcreteStep n (cstarOnsiteHamiltonian w n) + w n • cstarTailZ n‖ ≤
          ‖cstarConcreteStep n (cstarOnsiteHamiltonian w n)‖ + ‖w n • cstarTailZ n‖ :=
        norm_add_le _ _
      _ ≤ ‖cstarOnsiteHamiltonian w n‖ + |w n| := by
        rw [← Complex.coe_smul (w n) (cstarTailZ n), norm_smul,
          Complex.norm_real, Real.norm_eq_abs, cstarTailZ_norm, mul_one]
        exact add_le_add (cstarConcreteStep_norm_le n (cstarOnsiteHamiltonian w n)) (le_refl _)
      _ ≤ (∑ j ∈ Finset.range n, |w j|) + |w n| := add_le_add ih (le_refl _)

/-- The actual absolute sum controls every stage, with no additional bound assumption. -/
theorem cstarOnsiteHamiltonian_norm_le_tsum (w : ℕ → ℝ)
    (hw : Summable (fun j => |w j|)) (n : ℕ) :
    ‖cstarOnsiteHamiltonian w n‖ ≤ ∑' j, |w j| :=
  (cstarOnsiteHamiltonian_norm_le_sum w n).trans
    (hw.sum_le_tsum (Finset.range n) (fun j _ => abs_nonneg (w j)))

end InfoGeometry.Canonical.GrowingOnsiteMatrixNorm

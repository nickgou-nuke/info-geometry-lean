/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Algebra.CyclotomicOperatorProjectors
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.RingTheory.Idempotents

/-!
# Krein Dirac blocks and normalization by a commuting unit

The signed block acts on the full doubled module over a possibly
noncommutative star ring. Its square retains both ordered Gram products and
both commutators. Diagonal cancellation alone does not imply square zero.

The normalization theorem assumes an invertible commuting gap and the exact
square relation. It constructs an algebraic involution and reuses the existing
involution projectors. No order, positive metric, analytic spectrum, or
physical CPT interpretation is inferred from these hypotheses.
-/

namespace InfoGeometry.Physics.KreinDiracBlock

open Matrix
open InfoGeometry.Algebra.CyclotomicOperatorProjectors

section SignedBlock

variable {B : Type*} [Ring B] [StarRing B]

/-- The negative lower-block Dirac operator on the native doubled carrier. -/
def diracBlock (m b : B) : BdGBlock B :=
  !![m, b; -star b, -m]

/-- The complete square, with no commutativity or normality assumptions. -/
theorem diracBlock_sq (m b : B) :
    diracBlock m b * diracBlock m b =
      !![m * m - b * star b, m * b - b * m;
         m * star b - star b * m, m * m - star b * b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracBlock, Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

/-- Square zero requires both diagonal equalities and both commutations. -/
theorem diracBlock_sq_eq_zero_iff (m b : B) :
    diracBlock m b * diracBlock m b = 0 ↔
      m * m = b * star b ∧ m * m = star b * b ∧
        Commute m b ∧ Commute m (star b) := by
  rw [diracBlock_sq]
  constructor
  · intro h
    have h00 := congrArg (fun X : BdGBlock B => X 0 0) h
    have h11 := congrArg (fun X : BdGBlock B => X 1 1) h
    have h01 := congrArg (fun X : BdGBlock B => X 0 1) h
    have h10 := congrArg (fun X : BdGBlock B => X 1 0) h
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact sub_eq_zero.mp (by simpa using h00)
    · exact sub_eq_zero.mp (by simpa using h11)
    · change m * b = b * m
      exact sub_eq_zero.mp (by simpa using h01)
    · change m * star b = star b * m
      exact sub_eq_zero.mp (by simpa using h10)
  · rintro ⟨h00, h11, h01, h10⟩
    ext i j
    fin_cases i <;> fin_cases j
    · change m * m - b * star b = 0
      exact sub_eq_zero.mpr h00
    · change m * b - b * m = 0
      exact sub_eq_zero.mpr h01.eq
    · change m * star b - star b * m = 0
      exact sub_eq_zero.mpr h10.eq
    · change m * m - star b * b = 0
      exact sub_eq_zero.mpr h11

/-- A self-adjoint mass gives self-adjointness for the chiral metric. -/
theorem diracBlock_krein_selfAdjoint (m b : B) (hm : star m = m) :
    chiralGrading * star (diracBlock m b) * chiralGrading = diracBlock m b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralGrading, diracBlock, Matrix.mul_apply, Fin.sum_univ_two, hm]

/-- If the mass is self-adjoint, commuting with `b` also gives the second
commutation, but both diagonal Gram products must still be checked. -/
theorem diracBlock_sq_eq_zero_iff_of_selfAdjoint
    (m b : B) (hm : star m = m) :
    diracBlock m b * diracBlock m b = 0 ↔
      m * m = b * star b ∧ m * m = star b * b ∧ Commute m b := by
  rw [diracBlock_sq_eq_zero_iff]
  constructor
  · rintro ⟨h00, h11, h01, _⟩
    exact ⟨h00, h11, h01⟩
  · rintro ⟨h00, h11, h01⟩
    refine ⟨h00, h11, h01, ?_⟩
    change m * star b = star b * m
    simpa only [star_mul, hm] using (congrArg star h01.eq).symm

end SignedBlock

section UnitNormalization

variable {R : Type*} [Monoid R]

/-- Right normalization by an actual unit, preserving the specified order. -/
def normalizeByUnit (D : R) (gap : Rˣ) : R := D * (↑(gap⁻¹) : R)

/-- Normalization has an exact right reconstruction law. -/
theorem normalizeByUnit_mul_gap (D : R) (gap : Rˣ) :
    normalizeByUnit D gap * (gap : R) = D := by
  simp [normalizeByUnit, mul_assoc]

/-- A commuting unit with the same square normalizes the operator to an
involution. Neither centrality in the whole ring nor scalarization is used. -/
theorem normalizeByUnit_sq_eq_one
    (D : R) (gap : Rˣ) (hcomm : Commute D (gap : R))
    (hsq : D ^ 2 = (gap : R) ^ 2) :
    normalizeByUnit D gap ^ 2 = 1 := by
  have hinv : Commute D (↑(gap⁻¹) : R) := hcomm.units_inv_right
  rw [normalizeByUnit, hinv.mul_pow, hsq, ← gap.commute_coe_inv.mul_pow]
  simp

end UnitNormalization

section Projectors

variable {R : Type*} [Ring R]

/-- The existing involution projectors form a native complete orthogonal
family. The half-element must commute with the normalized operator. -/
theorem normalizeByUnit_projectors_complete
    (D : R) (gap : Rˣ) (hcomm : Commute D (gap : R))
    (hsq : D ^ 2 = (gap : R) ^ 2)
    (half : R) (hhalf : 2 * half = 1)
    (hhalfcomm : Commute half (normalizeByUnit D gap)) :
    CompleteOrthogonalIdempotents
      ![involutionPlusProjector (normalizeByUnit D gap) half,
        involutionMinusProjector (normalizeByUnit D gap) half] := by
  have hnormalized := normalizeByUnit_sq_eq_one D gap hcomm hsq
  apply CompleteOrthogonalIdempotents.pair_iff.mpr
  constructor
  · exact involution_plus_isIdempotent_of_commute hhalf hhalfcomm hnormalized
  · have hsum := involution_projectors_sum_eq_one
      (u := normalizeByUnit D gap) hhalf
    calc
      involutionMinusProjector (normalizeByUnit D gap) half =
          (involutionPlusProjector (normalizeByUnit D gap) half +
            involutionMinusProjector (normalizeByUnit D gap) half) -
            involutionPlusProjector (normalizeByUnit D gap) half := by abel
      _ = 1 - involutionPlusProjector (normalizeByUnit D gap) half := by rw [hsum]

/-- The normalized operator acts by the two defining eigenvalues on the
same projectors, using the arbitrary-ring projector owner. -/
theorem normalizeByUnit_projector_actions
    (D : R) (gap : Rˣ) (hcomm : Commute D (gap : R))
    (hsq : D ^ 2 = (gap : R) ^ 2) (half : R)
    (hhalfcomm : Commute half (normalizeByUnit D gap)) :
    normalizeByUnit D gap * involutionPlusProjector (normalizeByUnit D gap) half =
        involutionPlusProjector (normalizeByUnit D gap) half ∧
      normalizeByUnit D gap * involutionMinusProjector (normalizeByUnit D gap) half =
        -involutionMinusProjector (normalizeByUnit D gap) half := by
  have hnormalized := normalizeByUnit_sq_eq_one D gap hcomm hsq
  exact ⟨involution_plus_projector_eigen_of_commute hhalfcomm hnormalized,
    involution_minus_projector_eigen_of_commute hhalfcomm hnormalized⟩

variable [Algebra ℝ R]

/-- In a real algebra, the actual scalar half supplies the commuting
half-element. This applies directly to `BdGBlock B` over a real algebra `B`. -/
theorem normalizeByUnit_real_projectors_complete
    (D : R) (gap : Rˣ) (hcomm : Commute D (gap : R))
    (hsq : D ^ 2 = (gap : R) ^ 2) :
    CompleteOrthogonalIdempotents
      ![involutionPlusProjector (normalizeByUnit D gap) (algebraMap ℝ R (1 / 2)),
        involutionMinusProjector (normalizeByUnit D gap) (algebraMap ℝ R (1 / 2))] := by
  apply normalizeByUnit_projectors_complete D gap hcomm hsq
  · calc
      (2 : R) * algebraMap ℝ R (1 / 2) =
          algebraMap ℝ R ((2 : ℝ) * (1 / 2)) := by simp
      _ = 1 := by norm_num
  · exact Algebra.commutes (1 / 2 : ℝ) (normalizeByUnit D gap)

end Projectors

end InfoGeometry.Physics.KreinDiracBlock

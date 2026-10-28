/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CenteredBKMCommutatorGeometry
import InfoGeometry.Canonical.DikinFiniteOrbitColimit

/-!
# BKM commutator energy in the self-adjoint Dikin carrier

For self-adjoint operators `X` and `Y`, the commutator is skew-adjoint, while
`I • (X * Y - Y * X)` belongs to Mathlib's native self-adjoint subtype.
Simultaneous multiplication by `I` preserves the genuine sesquilinear
Kubo--Mori pairing. This identifies the existing BKM Dikin quadratic of the
self-adjoint commutator with the centered energy of the original commutator.

The distinction between these two arguments is intentional: real centering
fixes the skew-adjoint commutator, but need not fix its self-adjoint rotation.
The results concern operator quadratic geometry. They do not assert that a
BKM ellipsoid is contained in the positive-density cone.
-/

noncomputable section

namespace InfoGeometry.Canonical.BKMCommutatorDikin

open SouriauOnsagerBKM
open InfoGeometry.Canonical.CenteredBKMCommutatorGeometry
open InfoGeometry.Canonical.DikinFiniteOrbitColimit
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance

variable {n : ℕ}

/-- The complex structure preserves the ordered Kubo--Mori integrand in both
arguments. No observables are required to commute with the density. -/
theorem kuboMoriIntegrand_I_smul
    (D : FaithfulDensityOperator n) (A B : FiniteOperatorAlgebra n) (s : ℝ) :
    D.kuboMoriIntegrand (Complex.I • A) (Complex.I • B) s =
      D.kuboMoriIntegrand A B s := by
  unfold FaithfulDensityOperator.kuboMoriIntegrand
  congr 1
  simp [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Simultaneous multiplication by `I` preserves the native integral pairing. -/
theorem kuboMoriPairing_I_smul
    (D : FaithfulDensityOperator n) (A B : FiniteOperatorAlgebra n) :
    D.kuboMoriPairing (Complex.I • A) (Complex.I • B) =
      D.kuboMoriPairing A B := by
  unfold FaithfulDensityOperator.kuboMoriPairing
  apply intervalIntegral.integral_congr
  intro s _
  exact kuboMoriIntegrand_I_smul D A B s

/-- The real BKM form inherits simultaneous complex-structure invariance. -/
theorem bkmRealBilinForm_I_smul
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) :
    D.bkmRealBilinForm hpow (Complex.I • A) (Complex.I • B) =
      D.bkmRealBilinForm hpow A B := by
  simp only [FaithfulDensityOperator.bkmRealBilinForm_apply,
    kuboMoriPairing_I_smul]

/-- The commutator of two self-adjoint directions, rotated into the native
self-adjoint carrier by the complex structure. -/
def selfAdjointCommutator (X Y : SelfAdjointOperator n) : SelfAdjointOperator n :=
  ⟨Complex.I • (X.1 * Y.1 - Y.1 * X.1), by
    change star (Complex.I • (X.1 * Y.1 - Y.1 * X.1)) = _
    rw [star_smul, star_commutator_of_isSelfAdjoint X.1 Y.1 X.property Y.property]
    simp only [Complex.star_def, Complex.conj_I, neg_smul, smul_neg, neg_neg]⟩

@[simp] theorem selfAdjointCommutator_val (X Y : SelfAdjointOperator n) :
    (selfAdjointCommutator X Y).1 = Complex.I • (X.1 * Y.1 - Y.1 * X.1) :=
  rfl

/-- The self-adjoint commutator vanishes exactly for commuting directions. -/
theorem selfAdjointCommutator_eq_zero_iff (X Y : SelfAdjointOperator n) :
    selfAdjointCommutator X Y = 0 ↔ Commute X.1 Y.1 := by
  constructor
  · intro hzero
    have hval := congrArg Subtype.val hzero
    change Complex.I • (X.1 * Y.1 - Y.1 * X.1) = 0 at hval
    have hcomm : X.1 * Y.1 - Y.1 * X.1 = 0 :=
      (smul_eq_zero.mp hval).resolve_left Complex.I_ne_zero
    exact sub_eq_zero.mp hcomm
  · intro hcomm
    apply Subtype.ext
    simp [selfAdjointCommutator, sub_eq_zero.mpr hcomm.eq]

/-- The existing Dikin quadratic of the self-adjoint commutator is the full
uncentered BKM energy of the original skew-adjoint commutator. -/
theorem bkmDikinQuadratic_selfAdjointCommutator
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (X Y : SelfAdjointOperator n) :
    bkmDikinQuadratic D hpow (selfAdjointCommutator X Y) =
      D.bkmRealBilinForm hpow (X.1 * Y.1 - Y.1 * X.1)
        (X.1 * Y.1 - Y.1 * X.1) := by
  exact bkmRealBilinForm_I_smul D hpow _ _

/-- Centering fixes the original skew-adjoint commutator, so its centered
covariance is exactly the Dikin quadratic after self-adjoint rotation. -/
theorem bkmDikinQuadratic_selfAdjointCommutator_eq_centeredBKM
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (X Y : SelfAdjointOperator n) :
    bkmDikinQuadratic D hpow (selfAdjointCommutator X Y) =
      centeredBKMRealCovariance D hpow (X.1 * Y.1 - Y.1 * X.1)
        (X.1 * Y.1 - Y.1 * X.1) := by
  rw [bkmDikinQuadratic_selfAdjointCommutator]
  exact (centeredBKM_commutator_eq_bkm_of_isSelfAdjoint
    D hpow X.1 Y.1 X.property Y.property).symm

/-- Zero Dikin commutator energy is equivalent to commutativity. -/
theorem bkmDikinQuadratic_selfAdjointCommutator_eq_zero_iff
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (X Y : SelfAdjointOperator n) :
    bkmDikinQuadratic D hpow (selfAdjointCommutator X Y) = 0 ↔
      Commute X.1 Y.1 := by
  rw [bkmDikinQuadratic_eq_zero_iff, selfAdjointCommutator_eq_zero_iff]

/-- Every noncommuting self-adjoint pair has strictly positive Dikin energy. -/
theorem bkmDikinQuadratic_selfAdjointCommutator_pos_iff
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (X Y : SelfAdjointOperator n) :
    0 < bkmDikinQuadratic D hpow (selfAdjointCommutator X Y) ↔
      ¬ Commute X.1 Y.1 := by
  constructor
  · intro hpos hcomm
    have hzero :=
      (bkmDikinQuadratic_selfAdjointCommutator_eq_zero_iff D hpow X Y).mpr hcomm
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  · intro hcomm
    apply bkmDikinQuadratic_pos_of_ne_zero
    intro hzero
    exact hcomm ((selfAdjointCommutator_eq_zero_iff X Y).mp hzero)

/-- Membership of the rotated commutator in a BKM Dikin ellipsoid is the
corresponding bound on the centered energy of the original commutator. -/
theorem selfAdjointCommutator_mem_dikin_iff_centeredBKM_le
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (X Y : SelfAdjointOperator n) (r : ℝ) :
    InBkmDikinEllipsoid D hpow (selfAdjointCommutator X Y) r ↔
      centeredBKMRealCovariance D hpow (X.1 * Y.1 - Y.1 * X.1)
        (X.1 * Y.1 - Y.1 * X.1) ≤ r ^ 2 := by
  unfold InBkmDikinEllipsoid
  rw [bkmDikinQuadratic_selfAdjointCommutator_eq_centeredBKM]

/-- A zero-radius BKM Dikin constraint on the rotated commutator is exactly
commutativity of the original self-adjoint directions. -/
theorem selfAdjointCommutator_mem_dikin_zero_iff
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (X Y : SelfAdjointOperator n) :
    InBkmDikinEllipsoid D hpow (selfAdjointCommutator X Y) 0 ↔
      Commute X.1 Y.1 := by
  change bkmDikinQuadratic D hpow (selfAdjointCommutator X Y) ≤ (0 : ℝ) ^ 2 ↔ _
  rw [zero_pow (by decide : (2 : ℕ) ≠ 0)]
  constructor
  · intro hle
    exact (bkmDikinQuadratic_selfAdjointCommutator_eq_zero_iff D hpow X Y).mp
      (le_antisymm hle (bkmDikinQuadratic_nonneg D hpow _))
  · intro hcomm
    rw [(bkmDikinQuadratic_selfAdjointCommutator_eq_zero_iff D hpow X Y).mpr hcomm]

section NoncommutingWitness

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
open InfoGeometry.Algebra.MatrixNoncommutativity

/-- The existing coordinate realization preserves matrix self-adjointness. -/
theorem matrixOp_isSelfAdjoint
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsSelfAdjoint M) :
    IsSelfAdjoint (matrixOp M) := by
  change star (matrixOp M) = matrixOp M
  apply matrixOfOp_injective
  change matrixOfOp (ContinuousLinearMap.adjoint (matrixOp M)) = matrixOfOp (matrixOp M)
  simpa only [matrixOfOp_adjoint, matrixOfOp_matrixOp, Matrix.star_eq_conjTranspose]
    using hM.star_eq

/-- The shared non-diagonal Hermitian matrix witnesses remain noncommuting
after realization in the self-adjoint bounded-operator carrier. -/
theorem exists_noncommuting_selfAdjointOperators :
    ∃ X Y : SelfAdjointOperator 2, ¬ Commute X.1 Y.1 := by
  let X : SelfAdjointOperator 2 :=
    ⟨matrixOp (swapMatrix (A := ℂ)), matrixOp_isSelfAdjoint _ star_swapMatrix⟩
  let Y : SelfAdjointOperator 2 :=
    ⟨matrixOp (tiltedMatrix (A := ℂ)), matrixOp_isSelfAdjoint _ star_tiltedMatrix⟩
  refine ⟨X, Y, ?_⟩
  intro hcomm
  have hm := congrArg matrixOfOp hcomm.eq
  change
    matrixOfOp ((matrixOp (swapMatrix (A := ℂ))).comp
      (matrixOp (tiltedMatrix (A := ℂ)))) =
    matrixOfOp ((matrixOp (tiltedMatrix (A := ℂ))).comp
      (matrixOp (swapMatrix (A := ℂ)))) at hm
  simp only [matrixOfOp_comp, matrixOfOp_matrixOp] at hm
  exact swapMatrix_mul_tiltedMatrix_ne hm

/-- Every faithful two-dimensional density detects a concrete noncommuting
self-adjoint pair through strictly positive Dikin commutator energy. -/
theorem exists_positive_commutator_dikin_energy
    (D : FaithfulDensityOperator 2) (hpow : Continuous D.rpow) :
    ∃ X Y : SelfAdjointOperator 2,
      0 < bkmDikinQuadratic D hpow (selfAdjointCommutator X Y) := by
  obtain ⟨X, Y, hcomm⟩ := exists_noncommuting_selfAdjointOperators
  exact ⟨X, Y, (bkmDikinQuadratic_selfAdjointCommutator_pos_iff D hpow X Y).mpr hcomm⟩

end NoncommutingWitness

end InfoGeometry.Canonical.BKMCommutatorDikin

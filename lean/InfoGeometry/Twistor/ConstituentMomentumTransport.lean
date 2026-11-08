/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorInternalSymmetry
import Mathlib.Analysis.Matrix.PosDef

/-! # Momentum readout of the existing constituent tensor

Contract: on `Packet ι`, recover the sum of lower-spinor momenta from the
upper-right kinematic block, with epsilon index raising undone. The existing
unitary-mixing/skew-shift theorem then preserves momentum and its determinant.
This does not classify the stabilizer or change the constituent carrier.
-/
noncomputable section
namespace InfoGeometry.Twistor.ConstituentMomentumTransport

open PenroseIncidence TwistorKinematicTensor TwistorConstituentKinematics
open TwistorInternalSymmetry
open scoped Matrix ComplexOrder

/-- Undo the existing epsilon raising on the upper-right tensor block. -/
def momentumReadout (K : KinematicMatrix) : ComplexSpacetime :=
  fun a b => if a = 0 then -K (.inl 1) (.inr b) else K (.inl 0) (.inr b)

/-- The incoming spinor-first momentum convention is the transpose of the local one. -/
theorem incomingMomentum_eq_transpose (Z : Twistor4) :
    Matrix.vecMulVec Z.2 (star Z.2) = (momentum Z)ᵀ := by
  ext a b
  simp [momentum, Matrix.vecMulVec, Matrix.transpose_apply, mul_comm]

/-- Both momentum conventions have the same nonnegative real trace. -/
theorem momentum_trace (Z : Twistor4) :
    (Matrix.trace (momentum Z)).re =
      Complex.normSq (Z.2 0) + Complex.normSq (Z.2 1) := by
  simp [momentum, Matrix.trace, Matrix.vecMulVec, Fin.sum_univ_two,
    Complex.mul_re, Complex.normSq_apply]

/-- A nonzero lower spinor has strictly positive momentum trace. -/
theorem momentum_trace_positive (Z : Twistor4) (hZ : Z.2 ≠ 0) :
    0 < (Matrix.trace (momentum Z)).re := by
  rw [momentum_trace]
  have h0 := Complex.normSq_nonneg (Z.2 0)
  have h1 := Complex.normSq_nonneg (Z.2 1)
  by_contra hn
  have hz0 : Complex.normSq (Z.2 0) = 0 := by linarith
  have hz1 : Complex.normSq (Z.2 1) = 0 := by linarith
  apply hZ
  funext i
  fin_cases i
  · exact Complex.normSq_eq_zero.mp hz0
  · exact Complex.normSq_eq_zero.mp hz1

/-- Unit-norm phase scaling fixes the local conjugate-first momentum convention. -/
theorem momentum_phase (c : ℂ) (hc : c * star c = 1) (Z : Twistor4) :
    momentum (c • Z) = momentum Z := by
  have hc' : star c * c = 1 := by rwa [mul_comm]
  ext a b
  change star (c * Z.2 a) * (c * Z.2 b) = star (Z.2 a) * Z.2 b
  rw [star_mul]
  calc
    star (Z.2 a) * star c * (c * Z.2 b) =
        (star c * c) * (star (Z.2 a) * Z.2 b) := by ring
    _ = _ := by rw [hc', one_mul]

/-- The upstream massive-pair witness retains nullness and the full matrix sum. -/
theorem two_null_constituents_massive :
    ∃ Z W : Twistor4,
      (momentum Z).det = 0 ∧ (momentum W).det = 0 ∧
      momentum Z + momentum W = 1 ∧ pairMassSq Z W = 1 := by
  let Z : Twistor4 := (0, ![1, 0])
  let W : Twistor4 := (0, ![0, 1])
  refine ⟨Z, W, momentum_null Z, momentum_null W, ?_, massive_pair_witness⟩
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [momentum, Matrix.vecMulVec, Z, W]

/-- The angular block remains symmetric with the local physical normalization. -/
theorem angularSpinor_symmetric (Z : Twistor4) : (angularSpinor Z)ᵀ = angularSpinor Z := by
  ext a b
  simp only [Matrix.transpose_apply, angularSpinor]
  ring

variable {ι : Type*} [Fintype ι]

/-- The local momentum is a Gram matrix of the actual lower-spinor rows. -/
theorem totalMomentum_gram (Z : Packet ι) :
    totalMomentum Z =
      (show Matrix ι (Fin 2) ℂ from fun i a => (Z i).2 a)ᴴ *
        (show Matrix ι (Fin 2) ℂ from fun i a => (Z i).2 a) := by
  ext a b
  change (∑ i, momentum (Z i)) a b = ∑ i, star ((Z i).2 a) * (Z i).2 b
  simp [momentum, Matrix.vecMulVec, Matrix.sum_apply]

/-- Positive semidefiniteness holds for the whole momentum matrix. -/
theorem totalMomentum_posSemidef (Z : Packet ι) :
    (totalMomentum Z).PosSemidef := by
  rw [totalMomentum_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Infinity shifts leave the lower spinors unchanged without a skewness premise. -/
theorem shift_momentum (L : Matrix ι ι ℂ) (Z : Packet ι) :
    totalMomentum (shift L Z) = totalMomentum Z := by
  simp [totalMomentum, momentum, shift, infinityConjugate, Prod.snd_sum]

/-- Translation of incidence changes only upper spinors, so the pair mass is fixed. -/
theorem pairMassSq_translation (X : ComplexSpacetime) (Z W : Twistor4) :
    pairMassSq (InfinityTwistor.translation X Z) (InfinityTwistor.translation X W) =
      pairMassSq Z W := rfl

/-- The readout recovers the actual sum of constituent momenta. -/
theorem totalMomentum_readout (Z : Packet ι) :
    momentumReadout (totalKinematic Z) = totalMomentum Z := by
  ext a b
  fin_cases a <;>
    simp [momentumReadout, totalKinematic, totalMomentum, Matrix.sum_apply,
      kinematic_upper_lower, raiseSpinor, momentum, Matrix.vecMulVec]

variable [DecidableEq ι]

/-- The established internal transformation preserves the full momentum matrix. -/
theorem internalTransform_preserves_momentum (U L : Matrix ι ι ℂ)
    (hU : Uᴴ * U = 1) (hL : Lᵀ = -L) (Z : Packet ι) :
    totalMomentum (internalTransform U L Z) = totalMomentum Z := by
  rw [← totalMomentum_readout, internalTransform_kinematic U L hU hL,
    totalMomentum_readout]

/-- Its determinant, the same algebraic mass invariant, is preserved. -/
theorem internalTransform_preserves_mass (U L : Matrix ι ι ℂ)
    (hU : Uᴴ * U = 1) (hL : Lᵀ = -L) (Z : Packet ι) :
    (totalMomentum (internalTransform U L Z)).det = (totalMomentum Z).det := by
  rw [internalTransform_preserves_momentum U L hU hL]

end InfoGeometry.Twistor.ConstituentMomentumTransport

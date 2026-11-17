/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit
import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetFunctionalCalculus
import InfoGeometry.Quantum.BoundaryInstrument

/-!
# Observational entropy for a two-sheet projective coarse-graining

The state remains an arbitrary full complex matrix. Only the coarse-grained
reference is uniform on the two complementary projection ranges. There is no
commutation hypothesis between the input state and the projection.

For a positive trace-one input and a nontrivial star projection, the actual
matrix coarse-graining is positive, has trace one, and preserves both Born
probabilities. Native continuous functional calculus gives its logarithm and
the exact observational-entropy gap as a trace of the existing Umegaki kernel.

Zero-probability sheets annihilate the input on both sides. An explicit
factorization proves that the coarse-grained kernel is contained in the input
kernel, so zero eigenvalues do not conceal a support mismatch. Real.log is
total at zero; every zero-probability entropy contribution is zero.

No relative-entropy nonnegativity, equality rigidity, or monotonicity in time
is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetObservationalEntropy

open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open PolarFrameTraceDensity MatrixEntropyUnitaryOrbit
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- The Born trace pairing, retaining the original full matrix input. -/
def sheetProbability (ρ P : Mat) : ℝ := (Matrix.trace (ρ * P)).re

/-- Uniformization within each of the two actual projection ranges. -/
def coarseGrainedState (ρ P : Mat) : Mat :=
  twoSheet P (sheetProbability ρ P / traceMass P)
    (sheetProbability ρ (1 - P) / traceMass (1 - P))

/-- The trace dimension and probability contribution of each observed sheet. -/
def observationalEntropy (ρ P : Mat) : ℝ :=
  sheetProbability ρ P *
      (-Real.log (sheetProbability ρ P) + Real.log (traceMass P)) +
    sheetProbability ρ (1 - P) *
      (-Real.log (sheetProbability ρ (1 - P)) + Real.log (traceMass (1 - P)))

theorem traceMass_pos_of_posSemidef {A : Mat} (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    0 < traceMass A := by
  have htrace := Complex.nonneg_iff.mp hA.trace_nonneg
  have hmass : traceMass A ≠ 0 := by
    intro hz
    apply hA0
    apply hA.trace_eq_zero_iff.mp
    apply Complex.ext
    · exact hz
    · exact htrace.2.symm
  exact lt_of_le_of_ne htrace.1 hmass.symm

theorem projection_traceMass_pos {P : Mat} (hP : IsStarProjection P) (hP0 : P ≠ 0) :
    0 < traceMass P :=
  traceMass_pos_of_posSemidef hP.nonneg.posSemidef hP0

theorem complement_traceMass_pos {P : Mat} (hP : IsStarProjection P) (hP1 : P ≠ 1) :
    0 < traceMass (1 - P) :=
  projection_traceMass_pos hP.one_sub (sub_ne_zero.mpr hP1.symm)

theorem sheetProbability_nonneg {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) : 0 ≤ sheetProbability ρ P :=
  (Complex.nonneg_iff.mp
    (InfoGeometry.Quantum.BoundaryConditioning.trace_pairing_nonneg
      hρ hP.nonneg.posSemidef)).1

theorem sheetProbability_add_complement (ρ P : Mat) (hρ1 : Matrix.trace ρ = 1) :
    sheetProbability ρ P + sheetProbability ρ (1 - P) = 1 := by
  simp only [sheetProbability, mul_sub, mul_one, Matrix.trace_sub, Complex.sub_re,
    hρ1, Complex.one_re]
  abel

/-- Taking the trace does not replace the noncommutative input by a scalar state. -/
theorem trace_pairing_twoSheet (ρ P : Mat) (a b : ℝ) :
    (Matrix.trace (ρ * twoSheet P a b)).re =
      a * sheetProbability ρ P + b * sheetProbability ρ (1 - P) := by
  simp [twoSheet, sheetProbability, mul_add, Matrix.trace_smul]

theorem coarseGrainedState_mul_projection (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) :
    coarseGrainedState ρ P * P = (sheetProbability ρ P / traceMass P) • P := by
  simp only [coarseGrainedState, twoSheet, add_mul, smul_mul_assoc,
    hP.isIdempotentElem.eq, hP.one_sub_mul_self, smul_zero, add_zero]

theorem coarseGrainedState_mul_complement (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) :
    coarseGrainedState ρ P * (1 - P) =
      (sheetProbability ρ (1 - P) / traceMass (1 - P)) • (1 - P) := by
  simp only [coarseGrainedState, twoSheet, add_mul, smul_mul_assoc,
    hP.mul_one_sub_self, hP.one_sub.isIdempotentElem.eq, smul_zero, zero_add]

theorem sheetProbability_coarseGrainedState (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) (hP0 : P ≠ 0) :
    sheetProbability (coarseGrainedState ρ P) P = sheetProbability ρ P := by
  rw [sheetProbability, coarseGrainedState_mul_projection ρ hP]
  simpa only [Matrix.trace_smul, RCLike.smul_re, traceMass] using
    div_mul_cancel₀ (sheetProbability ρ P) (projection_traceMass_pos hP hP0).ne'

theorem sheetProbability_complement_coarseGrainedState (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) (hP1 : P ≠ 1) :
    sheetProbability (coarseGrainedState ρ P) (1 - P) =
      sheetProbability ρ (1 - P) := by
  rw [sheetProbability, coarseGrainedState_mul_complement ρ hP]
  simpa only [Matrix.trace_smul, RCLike.smul_re, traceMass] using
    div_mul_cancel₀ (sheetProbability ρ (1 - P))
      (complement_traceMass_pos hP hP1).ne'

theorem traceMass_coarseGrainedState (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    traceMass (coarseGrainedState ρ P) =
      sheetProbability ρ P + sheetProbability ρ (1 - P) := by
  calc
    traceMass (coarseGrainedState ρ P) =
        (sheetProbability ρ P / traceMass P) * traceMass P +
          (sheetProbability ρ (1 - P) / traceMass (1 - P)) * traceMass (1 - P) := by
      simp [coarseGrainedState, twoSheet, traceMass, Matrix.trace_smul]
    _ = _ := by
      rw [div_mul_cancel₀ _ (projection_traceMass_pos hP hP0).ne',
        div_mul_cancel₀ _ (complement_traceMass_pos hP hP1).ne']

theorem coarseGrainedState_posSemidef {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) : (coarseGrainedState ρ P).PosSemidef := by
  have hmassP : 0 ≤ traceMass P :=
    (Complex.nonneg_iff.mp hP.nonneg.posSemidef.trace_nonneg).1
  have hmassQ : 0 ≤ traceMass (1 - P) :=
    (Complex.nonneg_iff.mp hP.one_sub.nonneg.posSemidef.trace_nonneg).1
  exact
    (hP.nonneg.posSemidef.smul (div_nonneg (sheetProbability_nonneg hρ hP) hmassP)).add
      (hP.one_sub.nonneg.posSemidef.smul
        (div_nonneg (sheetProbability_nonneg hρ hP.one_sub) hmassQ))

theorem trace_coarseGrainedState {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hρ1 : Matrix.trace ρ = 1) (hP : IsStarProjection P) (hP0 : P ≠ 0)
    (hP1 : P ≠ 1) : Matrix.trace (coarseGrainedState ρ P) = 1 := by
  apply Complex.ext
  · change traceMass (coarseGrainedState ρ P) = 1
    rw [traceMass_coarseGrainedState ρ hP hP0 hP1,
      sheetProbability_add_complement ρ P hρ1]
  · exact (Complex.nonneg_iff.mp
      (coarseGrainedState_posSemidef hρ hP).trace_nonneg).2.symm

/-- The constructed full matrix is a normalized positive density. -/
theorem coarseGrainedState_isDensity {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hρ1 : Matrix.trace ρ = 1) (hP : IsStarProjection P) (hP0 : P ≠ 0)
    (hP1 : P ≠ 1) :
    (coarseGrainedState ρ P).PosSemidef ∧ Matrix.trace (coarseGrainedState ρ P) = 1 :=
  ⟨coarseGrainedState_posSemidef hρ hP,
    trace_coarseGrainedState hρ hρ1 hP hP0 hP1⟩

theorem coarseGrainedState_idempotent (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    coarseGrainedState (coarseGrainedState ρ P) P = coarseGrainedState ρ P := by
  change twoSheet P
      (sheetProbability (coarseGrainedState ρ P) P / traceMass P)
      (sheetProbability (coarseGrainedState ρ P) (1 - P) / traceMass (1 - P)) =
    twoSheet P (sheetProbability ρ P / traceMass P)
      (sheetProbability ρ (1 - P) / traceMass (1 - P))
  rw [sheetProbability_coarseGrainedState ρ hP hP0,
    sheetProbability_complement_coarseGrainedState ρ hP hP1]

theorem observationalEntropy_coarseGrainedState (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    observationalEntropy (coarseGrainedState ρ P) P = observationalEntropy ρ P := by
  simp only [observationalEntropy, sheetProbability_coarseGrainedState ρ hP hP0,
    sheetProbability_complement_coarseGrainedState ρ hP hP1]

private theorem weighted_neg_log_div (p d : ℝ) (hd : d ≠ 0) :
    (-Real.log (p / d)) * p = p * (-Real.log p + Real.log d) := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [Real.log_div hp hd]
    ring

/-- The actual CFC cross-entropy, including a sheet of probability zero. -/
theorem crossEntropy_eq_observationalEntropy (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    (Matrix.trace (ρ * (-CFC.log (coarseGrainedState ρ P)))).re =
      observationalEntropy ρ P := by
  rw [coarseGrainedState, neg_log_twoSheet hP, trace_pairing_twoSheet]
  rw [weighted_neg_log_div _ _ (projection_traceMass_pos hP hP0).ne',
    weighted_neg_log_div _ _ (complement_traceMass_pos hP hP1).ne']
  rfl

/-- Observational entropy is the native matrix entropy of the constructed reference. -/
theorem matrixEntropy_coarseGrainedState (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    matrixEntropy (coarseGrainedState ρ P) = observationalEntropy ρ P := by
  rw [matrixEntropy_eq_trace_negative_log]
  simpa only [coarseGrainedState_idempotent ρ hP hP0 hP1,
    observationalEntropy_coarseGrainedState ρ hP hP0 hP1] using
    crossEntropy_eq_observationalEntropy (coarseGrainedState ρ P) hP hP0 hP1

/-- The exact entropy gap is a trace of the existing ordered Umegaki kernel.
This identity alone does not assert that the trace is nonnegative. -/
theorem entropy_gap_eq_umegakiKernel (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    observationalEntropy ρ P - matrixEntropy ρ =
      (Matrix.trace (umegakiKernel ρ (coarseGrainedState ρ P))).re := by
  rw [← crossEntropy_eq_observationalEntropy ρ hP hP0 hP1, matrixEntropy_eq]
  simp only [umegakiKernel, relativeLogDensity, CFC.log, mul_sub, mul_neg,
    Matrix.trace_sub, Matrix.trace_neg, Complex.sub_re, Complex.neg_re]
  ring

/-- The same gap through the canonical positive trace functional. -/
theorem entropy_gap_eq_umegakiRelativeEntropy (ρ : Mat) {P : Mat}
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    observationalEntropy ρ P - matrixEntropy ρ =
      (umegakiRelativeEntropy (positiveTraceDensity (1 : Mat) zero_le_one)
        ρ (coarseGrainedState ρ P)).re := by
  simpa only [umegakiRelativeEntropy, positiveTraceDensity_apply, one_mul] using
    entropy_gap_eq_umegakiKernel ρ hP hP0 hP1

/-- A zero-probability projection annihilates a positive input, without
commuting the two matrices or assuming the input is faithful. -/
theorem sheetProbability_eq_zero_iff_projection_mul_eq_zero {ρ P : Mat}
    (hρ : ρ.PosSemidef) (hP : IsStarProjection P) :
    sheetProbability ρ P = 0 ↔ P * ρ = 0 := by
  have hs := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  have hgram :
      Matrix.trace ((P * CFC.sqrt ρ) * star (P * CFC.sqrt ρ)) =
        Matrix.trace (ρ * P) := by
    simp only [star_mul, hs.star_eq, hP.isSelfAdjoint.star_eq]
    calc
      Matrix.trace (P * CFC.sqrt ρ * (CFC.sqrt ρ * P)) =
          Matrix.trace (P * (CFC.sqrt ρ * CFC.sqrt ρ) * P) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (P * ρ * P) := by rw [CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
      _ = Matrix.trace (P * P * ρ) := Matrix.trace_mul_cycle P ρ P
      _ = Matrix.trace (ρ * P) := by
        rw [hP.isIdempotentElem.eq, Matrix.trace_mul_comm]
  constructor
  · intro hp
    have hC : P * CFC.sqrt ρ = 0 := by
      apply (InfoGeometry.Quantum.BoundaryInstrument.gram_trace_re_eq_zero_iff
        (P * CFC.sqrt ρ)).mp
      rw [hgram]
      exact hp
    calc
      P * ρ = P * (CFC.sqrt ρ * CFC.sqrt ρ) := by
        rw [CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
      _ = (P * CFC.sqrt ρ) * CFC.sqrt ρ := (mul_assoc _ _ _).symm
      _ = 0 := by rw [hC, zero_mul]
  · intro hzero
    simp only [sheetProbability, Matrix.trace_mul_comm ρ P, hzero,
      Matrix.trace_zero, Complex.zero_re]

theorem sheetProbability_eq_zero_iff_mul_projection_eq_zero {ρ P : Mat}
    (hρ : ρ.PosSemidef) (hP : IsStarProjection P) :
    sheetProbability ρ P = 0 ↔ ρ * P = 0 := by
  rw [sheetProbability_eq_zero_iff_projection_mul_eq_zero hρ hP]
  constructor <;> intro hzero
  · simpa only [star_mul, hρ.isHermitian.star_eq, hP.isSelfAdjoint.star_eq,
      star_zero] using congrArg star hzero
  · simpa only [star_mul, hρ.isHermitian.star_eq, hP.isSelfAdjoint.star_eq,
      star_zero] using congrArg star hzero

private theorem reconstruct_sheet {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) :
    ((traceMass P / sheetProbability ρ P) *
      (sheetProbability ρ P / traceMass P)) • (ρ * P) = ρ * P := by
  by_cases hp : sheetProbability ρ P = 0
  · have hz := (sheetProbability_eq_zero_iff_mul_projection_eq_zero hρ hP).mp hp
    simp only [hz, smul_zero]
  · have hd : traceMass P ≠ 0 := (projection_traceMass_pos hP hP0).ne'
    have hcoeff : (traceMass P / sheetProbability ρ P) *
        (sheetProbability ρ P / traceMass P) = 1 := by
      rw [div_mul_div_cancel₀ hp, div_self hd]
    rw [hcoeff, one_smul]

/-- The explicit reciprocal sheet operator acts only on the support of the
input. Division by a zero probability causes no loss because that sheet
already annihilates the input. -/
theorem coarseGrainedState_support_factorization {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ρ * twoSheet P (traceMass P / sheetProbability ρ P)
        (traceMass (1 - P) / sheetProbability ρ (1 - P)) *
      coarseGrainedState ρ P = ρ := by
  rw [mul_assoc, coarseGrainedState, twoSheet_mul P hP.isIdempotentElem.eq]
  simp only [twoSheet, mul_add, mul_smul_comm]
  rw [reconstruct_sheet hρ hP hP0,
    reconstruct_sheet hρ hP.one_sub (sub_ne_zero.mpr hP1.symm)]
  rw [mul_sub, mul_one]
  abel

/-- Every vector killed by the coarse-grained state is killed by the input. -/
theorem coarseGrainedState_mulVec_eq_zero_implies {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    {v : n → ℂ} (hv : coarseGrainedState ρ P *ᵥ v = 0) : ρ *ᵥ v = 0 := by
  calc
    ρ *ᵥ v =
        (ρ * twoSheet P (traceMass P / sheetProbability ρ P)
          (traceMass (1 - P) / sheetProbability ρ (1 - P)) *
          coarseGrainedState ρ P) *ᵥ v := by
      rw [coarseGrainedState_support_factorization hρ hP hP0 hP1]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- The native linear-map kernel inclusion is the finite-dimensional support condition. -/
theorem coarseGrainedState_kernel_le {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    LinearMap.ker (coarseGrainedState ρ P).mulVecLin ≤ LinearMap.ker ρ.mulVecLin := by
  intro v hv
  change ρ *ᵥ v = 0
  apply coarseGrainedState_mulVec_eq_zero_implies hρ hP hP0 hP1
  exact hv

end InfoGeometry.Canonical.TwoSheetObservationalEntropy

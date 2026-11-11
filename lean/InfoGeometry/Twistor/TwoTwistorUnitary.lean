/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwoTwistorInfinityBlocks
import InfoGeometry.Twistor.TwoTwistorSpinCayley
import InfoGeometry.Twistor.ConstituentMomentumTransport

/-!
# Right constituent-frame changes on the two-twistor invariants

The column convention is implemented by transposing the existing row-mixing
action. Unitary changes preserve the entire momentum matrix and conjugate the
Witt Gram matrix. Determinant-one changes preserve the actual bivector.
The Pauli coefficients are internal Gram coordinates; no spacetime spin
operator or little-group classification is inferred from their covariance.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwoTwistorUnitary

open PenroseIncidence PerjesConventions TwistorKinematicTensor
open TwistorConstituentKinematics TwistorInternalSymmetry
open ConstituentMomentumTransport ConstituentColumnEquivalence
open TwoTwistorGramMass TwoTwistorInfinityBlocks TwoTwistorSpinCayley
open scoped Matrix

/-- Right action on column frames, expressed using the existing packet action. -/
def changeFrame (U : ComplexSpacetime) (Z : PairFrame) : PairFrame := mix Uᵀ Z

theorem changeFrame_one (Z : PairFrame) : changeFrame 1 Z = Z := by
  simp [changeFrame, mix_one]

/-- Successive right changes keep their order. -/
theorem changeFrame_mul (U V : ComplexSpacetime) (Z : PairFrame) :
    changeFrame V (changeFrame U Z) = changeFrame (U * V) Z := by
  simp [changeFrame, mix_mul, Matrix.transpose_mul]

theorem column_changeFrame (U : ComplexSpacetime) (Z : PairFrame) :
    columnEquiv (changeFrame U Z) = columnEquiv Z * U := by
  ext a i
  have h := column_mix Uᵀ Z (finSumFinEquiv.symm a) i
  simpa [changeFrame] using h

theorem gram_changeFrame (U : ComplexSpacetime) (Z : PairFrame) :
    gram (changeFrame U Z) = Uᴴ * gram Z * U := by
  ext i j
  simp [gram, changeFrame, mix, wittPair, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

theorem transpose_unitary (U : ComplexSpacetime) (hU : Uᴴ * U = 1) :
    (Uᵀ)ᴴ * Uᵀ = 1 := by
  have hr : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have ht := congrArg Matrix.transpose hr
  simpa only [Matrix.transpose_mul, Matrix.transpose_conjTranspose,
    Matrix.conjTranspose_transpose, Matrix.transpose_one] using ht

/-- Existing whole-momentum invariance, adapted to the right column convention. -/
theorem momentum_changeFrame (U : ComplexSpacetime) (hU : Uᴴ * U = 1)
    (Z : PairFrame) :
    totalMomentum (changeFrame U Z) = totalMomentum Z := by
  have h := internalTransform_preserves_momentum Uᵀ 0
    (transpose_unitary U hU) (by simp) Z
  simpa [internalTransform, shift_zero, changeFrame] using h

theorem paperMassSq_changeFrame (U : ComplexSpacetime) (hU : Uᴴ * U = 1)
    (Z : PairFrame) : paperMassSq (changeFrame U Z) = paperMassSq Z := by
  have hp := momentum_changeFrame U hU Z
  simp only [totalMomentum, Fin.sum_univ_two] at hp
  have hc : (paperMassSq (changeFrame U Z) : ℂ) = (paperMassSq Z : ℂ) := by
    rw [paperMassSq_eq_twice_momentum_det, hp, paperMassSq_eq_twice_momentum_det]
  exact_mod_cast hc

/-- The uncontracted two-tensor transforms by determinant, before any norm is taken. -/
theorem bivector_changeFrame (U : ComplexSpacetime) (Z : PairFrame) :
    bivector (changeFrame U Z) = U.det • bivector Z := by
  ext a b
  simp [bivector, changeFrame, mix, Matrix.det_fin_two, Fin.sum_univ_two,
    smul_eq_mul]
  ring

theorem bivector_changeFrame_det_one (U : ComplexSpacetime) (hU : U.det = 1)
    (Z : PairFrame) : bivector (changeFrame U Z) = bivector Z := by
  rw [bivector_changeFrame, hU, one_smul]

theorem gram_eq_hermitianCoordinates (Z : PairFrame) :
    gram Z = hermitianCoordinates (paperHelicity (Z 0))
      (paperHelicity (Z 1)) (wittPair (Z 0) (Z 1)) :=
  eq_hermitianCoordinates (gram Z) (gram_hermitian Z)

/-- The conformal determinant uses the two helicities and the cross pairing. -/
theorem gram_det_helicity (Z : PairFrame) :
    (gram Z).det = ((4 * paperHelicity (Z 0) * paperHelicity (Z 1) -
      Complex.normSq (wittPair (Z 0) (Z 1)) : ℝ) : ℂ) := by
  rw [gram_eq_hermitianCoordinates, Matrix.det_fin_two]
  simp [hermitianCoordinates, Complex.normSq_eq_conj_mul_self]
  rw [show (starRingEnd ℂ) (wittPair (Z 0) (Z 1)) =
    wittPair (Z 1) (Z 0) from wittPair_conj (Z 0) (Z 1)]
  ring

theorem spinNormSq_gram (Z : PairFrame) :
    spinNormSq (gram Z) =
      ((paperHelicity (Z 0) - paperHelicity (Z 1)) ^ 2 +
        Complex.normSq (wittPair (Z 0) (Z 1))) / 4 := by
  rw [gram_eq_hermitianCoordinates, spinNormSq_hermitianCoordinates]

theorem spinNormSq_changeFrame (U : ComplexSpacetime) (hU : Uᴴ * U = 1)
    (Z : PairFrame) :
    spinNormSq (gram (changeFrame U Z)) = spinNormSq (gram Z) := by
  rw [gram_changeFrame, spinNormSq_unitary_conjugate _ _ hU]

/-- The concrete Cayley change is isomassive and fixes the entire alternating tensor. -/
theorem cayley_preserves_pair (Z : PairFrame) :
    totalMomentum (changeFrame cayley Z) = totalMomentum Z ∧
      paperMassSq (changeFrame cayley Z) = paperMassSq Z ∧
      bivector (changeFrame cayley Z) = bivector Z ∧
      spinNormSq (gram (changeFrame cayley Z)) = spinNormSq (gram Z) := by
  exact ⟨momentum_changeFrame _ cayley_conjTranspose_mul Z,
    paperMassSq_changeFrame _ cayley_conjTranspose_mul Z,
    bivector_changeFrame_det_one _ cayley_det Z,
    spinNormSq_changeFrame _ cayley_conjTranspose_mul Z⟩

/-- A change in internal Gram coordinates at the same momentum and mass. -/
theorem cayley_gram_helicity_to_crossing (Z : PairFrame) (s : ℝ)
    (hZ : gram Z = hermitianCoordinates s (-s) 0) :
    gram (changeFrame cayley Z) = hermitianCoordinates 0 0 (2 * (s : ℂ)) := by
  rw [gram_changeFrame, hZ, cayley_helicity_to_crossing]

/-- Nonnegative mass in the explicitly stated paper normalization. -/
def paperMass (Z : PairFrame) : ℝ := Real.sqrt (paperMassSq Z)

theorem paperMass_sq (Z : PairFrame) : paperMass Z ^ 2 = paperMassSq Z :=
  Real.sq_sqrt (paperMassSq_nonneg Z)

theorem paperMass_pos (Z : PairFrame) (hZ : 0 < paperMassSq Z) :
    0 < paperMass Z := Real.sqrt_pos.mpr hZ

theorem paperMass_changeFrame (U : ComplexSpacetime) (hU : Uᴴ * U = 1)
    (Z : PairFrame) : paperMass (changeFrame U Z) = paperMass Z := by
  simp only [paperMass, paperMassSq_changeFrame U hU Z]

/-- Total real quotient of internal Pauli coordinates by mass. At zero mass
Lean's division is zero; physical pitch is interpreted only at positive mass. -/
def pitchVector (Z : PairFrame) : Fin 3 → ℝ :=
  fun i => spinVector (gram Z) i / paperMass Z

theorem pitchVector_sum_sq (Z : PairFrame) :
    ∑ i : Fin 3, pitchVector Z i ^ 2 = spinNormSq (gram Z) / paperMassSq Z := by
  simp only [pitchVector, div_pow]
  rw [← Finset.sum_div, paperMass_sq,
    ← spinNormSq_eq_sum_sq (gram Z) (gram_hermitian Z)]

/-- The squared pitch length is invariant; the vector is not asserted fixed. -/
theorem pitch_length_changeFrame (U : ComplexSpacetime) (hU : Uᴴ * U = 1)
    (Z : PairFrame) :
    (∑ i : Fin 3, pitchVector (changeFrame U Z) i ^ 2) =
      ∑ i : Fin 3, pitchVector Z i ^ 2 := by
  rw [pitchVector_sum_sq, pitchVector_sum_sq, spinNormSq_changeFrame U hU,
    paperMassSq_changeFrame U hU]

end InfoGeometry.Twistor.TwoTwistorUnitary

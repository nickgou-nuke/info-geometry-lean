/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.ConstituentWittGram
import InfoGeometry.Twistor.ConstituentColumnEquivalence
import InfoGeometry.Twistor.ConstituentMomentumTransport

/-!
# Right unitary mixing and the normalized Cayley Gram rotation

The right action on columns is the existing `mix Uᵀ`.  Its ordered inverse
laws, full momentum invariance, and Gram conjugation are proved on the same
packet.  The Cayley instance rotates a diagonal traceless Gram matrix to an
off-diagonal one while preserving its quadratic invariant.
-/

noncomputable section
namespace InfoGeometry.Twistor.ConstituentCayleyGram

open PenroseIncidence PerjesConventions TwistorKinematicTensor
open TwistorConstituentKinematics TwistorInternalSymmetry
open ConstituentWittGram ConstituentColumnEquivalence ConstituentMomentumTransport
open scoped BigOperators Matrix

section FinitePacket

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The native packet action becomes exactly right multiplication on columns. -/
theorem column_right_mix (U : Matrix ι ι ℂ) (Z : Packet ι) :
    columnEquiv (mix Uᵀ Z) = columnEquiv Z * U := by
  ext a i
  obtain ⟨s, rfl⟩ :=
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).surjective a
  simpa only [Matrix.transpose_transpose] using column_mix Uᵀ Z s i

theorem gram_right_mix (U : Matrix ι ι ℂ) (Z : Packet ι) :
    gram (mix Uᵀ Z) = Uᴴ * gram Z * U := by
  rw [gram_mix, Matrix.transpose_transpose]
  rfl

/-- Both inverse identities are obtained from the actual ordered mixing law. -/
theorem right_mix_inverse (U : Matrix ι ι ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) (Z : Packet ι) :
    mix (Uᴴ)ᵀ (mix Uᵀ Z) = Z ∧ mix Uᵀ (mix (Uᴴ)ᵀ Z) = Z := by
  constructor
  · rw [mix_mul, ← Matrix.transpose_mul, hright, Matrix.transpose_one, mix_one]
  · rw [mix_mul, ← Matrix.transpose_mul, hleft, Matrix.transpose_one, mix_one]

private theorem transpose_unitary (U : Matrix ι ι ℂ)
    (hU : U * Uᴴ = 1) : (Uᵀ)ᴴ * Uᵀ = 1 := by
  have h := congrArg Matrix.transpose hU
  rw [Matrix.transpose_mul] at h
  simpa only [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    Matrix.transpose_one] using h

/-- Preservation of the whole native momentum matrix, not only its determinant. -/
theorem momentum_right_mix (U : Matrix ι ι ℂ)
    (hU : U * Uᴴ = 1) (Z : Packet ι) :
    totalMomentum (mix Uᵀ Z) = totalMomentum Z := by
  have h := internalTransform_preserves_momentum Uᵀ (0 : Matrix ι ι ℂ)
    (transpose_unitary U hU) (by simp) Z
  simpa only [internalTransform, shift_zero] using h

theorem trace_gram_right_mix (U : Matrix ι ι ℂ)
    (hU : U * Uᴴ = 1) (Z : Packet ι) :
    Matrix.trace (gram (mix Uᵀ Z)) = Matrix.trace (gram Z) := by
  rw [gram_right_mix, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

end FinitePacket

/-- Traceless projection intertwines actual unitary conjugation. -/
theorem traceless_conjugate (U H : ComplexSpacetime)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) :
    traceless (Uᴴ * H * U) = Uᴴ * traceless H * U := by
  have ht : Matrix.trace (Uᴴ * H * U) = Matrix.trace H := by
    rw [Matrix.trace_mul_cycle, hright, Matrix.one_mul]
  unfold traceless
  rw [ht]
  simp only [Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc,
    Matrix.mul_one, hleft]

/-- The half-trace square is invariant under the same conjugation. -/
theorem tracelessQuadratic_conjugate (U H : ComplexSpacetime)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) :
    tracelessQuadratic (Uᴴ * H * U) = tracelessQuadratic H := by
  unfold tracelessQuadratic
  rw [traceless_conjugate U H hleft hright]
  have hsquare :
      (Uᴴ * traceless H * U) * (Uᴴ * traceless H * U) =
        Uᴴ * (traceless H * traceless H) * U := by
    calc
      _ = Uᴴ * traceless H * (U * Uᴴ) * traceless H * U := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hright]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hsquare, Matrix.trace_mul_cycle, hright, Matrix.one_mul]

/-- The normalized real Cayley matrix, viewed in the native complex matrix ring. -/
def cayley : ComplexSpacetime := paperScale • !![1, 1; -1, 1]

private theorem paperScale_star : star paperScale = paperScale := by
  simp [paperScale]

theorem cayley_conjTranspose_mul : cayleyᴴ * cayley = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayley, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, smul_eq_mul, paperScale_star] <;>
    linear_combination paperScale_sq

theorem cayley_mul_conjTranspose : cayley * cayleyᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayley, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, smul_eq_mul, paperScale_star] <;>
    linear_combination paperScale_sq

theorem cayley_det : cayley.det = 1 := by
  simp [cayley, Matrix.det_fin_two, smul_eq_mul]
  linear_combination paperScale_sq

/-- The positive off-diagonal sign follows from right multiplication by `cayley`. -/
theorem cayley_diagonal_conjugation (s : ℝ) :
    cayleyᴴ *
        !![((2 * s : ℝ) : ℂ), 0; 0, -((2 * s : ℝ) : ℂ)] * cayley =
      !![0, ((2 * s : ℝ) : ℂ); ((2 * s : ℝ) : ℂ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayley, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, smul_eq_mul, paperScale_star] <;>
    push_cast <;> ring_nf
  all_goals linear_combination (2 * (s : ℂ)) * paperScale_sq

theorem gram_cayley_of_diagonal (Z : Packet (Fin 2)) (s : ℝ)
    (hZ : gram Z =
      !![((2 * s : ℝ) : ℂ), 0; 0, -((2 * s : ℝ) : ℂ)]) :
    gram (mix cayleyᵀ Z) =
      !![0, ((2 * s : ℝ) : ℂ); ((2 * s : ℝ) : ℂ), 0] := by
  rw [gram_right_mix, hZ, cayley_diagonal_conjugation]

theorem cayley_preserves_momentum (Z : Packet (Fin 2)) :
    totalMomentum (mix cayleyᵀ Z) = totalMomentum Z :=
  momentum_right_mix cayley cayley_mul_conjTranspose Z

theorem cayley_preserves_tracelessQuadratic (Z : Packet (Fin 2)) :
    tracelessQuadratic (gram (mix cayleyᵀ Z)) = tracelessQuadratic (gram Z) := by
  rw [gram_right_mix]
  exact tracelessQuadratic_conjugate cayley (gram Z)
    cayley_conjTranspose_mul cayley_mul_conjTranspose

end InfoGeometry.Twistor.ConstituentCayleyGram

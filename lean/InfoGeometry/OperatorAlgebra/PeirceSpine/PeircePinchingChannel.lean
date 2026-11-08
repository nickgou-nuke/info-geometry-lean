/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum

/-!
# Peirce pinching as a finite-dimensional quantum channel

The causal order is: a self-adjoint idempotent supplies two Kraus operators;
their channel is the even Peirce projection; it is completely positive and
trace preserving; its off-diagonal kernel obstructs any universal left inverse.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleFiniteQuantum
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- The two complementary measurement operators. -/
def pinchingKraus (P : Mat) : Fin 2 → Mat := ![P, 1 - P]

theorem pinchingKraus_complete (P : Mat) (hP : P * P = P) (hPs : star P = P) :
    (∑ i, star (pinchingKraus P i) * pinchingKraus P i) = 1 := by
  rw [Fin.sum_univ_two]
  change star P * P + star (1 - P) * (1 - P) = 1
  rw [star_sub, star_one, hPs]
  peirce_nf hP

/-- The Kraus map is precisely the existing Peirce even projection. -/
theorem pinchingKraus_eq_even (P X : Mat) (hPs : star P = P) :
    InfoGeometry.Quantum.Choi.krausMap (pinchingKraus P) X = evenGrade P X := by
  change (∑ i, pinchingKraus P i * X * star (pinchingKraus P i)) = evenGrade P X
  rw [Fin.sum_univ_two]
  change P * X * star P + (1 - P) * X * star (1 - P) = evenGrade P X
  rw [star_sub, star_one, hPs]
  rfl

theorem pinching_trace (P X : Mat) (hP : P * P = P) (hPs : star P = P) :
    Matrix.trace (evenGrade P X) = Matrix.trace X := by
  rw [← pinchingKraus_eq_even P X hPs]
  exact InfoGeometry.Quantum.Choi.trace_krausMap_of_completeness
    (pinchingKraus P) (pinchingKraus_complete P hP hPs) X

/-- Complete positivity is certified for every finite ancillary dimension. -/
theorem pinching_completely_positive (P : Mat)
    {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × n) (r × n) ℂ) (hX : X.PosSemidef) :
    (InfoGeometry.Quantum.KrausAmplification.amplification (r := r)
      (InfoGeometry.Modular.Choi.krausChannel (pinchingKraus P)) X).PosSemidef :=
  InfoGeometry.Quantum.KrausAmplification.amplification_krausChannel_posSemidef
    (pinchingKraus P) X hX

theorem pinching_posSemidef (P X : Mat) (hPs : star P = P) (hX : X.PosSemidef) :
    (evenGrade P X).PosSemidef := by
  unfold evenGrade
  have h1 := hX.mul_mul_conjTranspose_same P
  have h2 := hX.mul_mul_conjTranspose_same (1 - P)
  change (P * X * star P).PosSemidef at h1
  change ((1 - P) * X * star (1 - P)).PosSemidef at h2
  rw [hPs] at h1
  rw [star_sub, star_one, hPs] at h2
  exact h1.add h2

theorem pinching_is_density (P X : Mat) (hP : P * P = P) (hPs : star P = P)
    (hX : X.PosSemidef) (hTrace : Matrix.trace X = 1) :
    (evenGrade P X).PosSemidef ∧ Matrix.trace (evenGrade P X) = 1 :=
  ⟨pinching_posSemidef P X hPs hX, (pinching_trace P X hP hPs).trans hTrace⟩

theorem pinching_idempotent (P X : Mat) (hP : P * P = P) :
    evenGrade P (evenGrade P X) = evenGrade P X := by
  unfold evenGrade
  peirce_nf hP

theorem pinching_kills_upper (P A : Mat) (hP : P * P = P) :
    evenGrade P (conePlus P A) = 0 := by
  unfold evenGrade conePlus
  peirce_nf hP

/-- If an off-diagonal corner is nonzero, no map on the full matrix algebra
can reverse pinching on every input. This includes all candidate channels. -/
theorem pinching_has_no_universal_left_inverse (P A : Mat) (hP : P * P = P)
    (hNonzero : conePlus P A ≠ 0) :
    ¬ ∃ recovery : Mat → Mat, ∀ X, recovery (evenGrade P X) = X := by
  rintro ⟨recovery, hRecovery⟩
  have h1 := hRecovery (conePlus P A)
  have h0 := hRecovery 0
  rw [pinching_kills_upper P A hP] at h1
  have hz : evenGrade P (0 : Mat) = 0 := by simp [evenGrade]
  rw [hz] at h0
  exact hNonzero (h1.symm.trans h0)

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel

end

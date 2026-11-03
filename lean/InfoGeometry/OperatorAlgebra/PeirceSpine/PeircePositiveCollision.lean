/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Basis

/-!
# Positive operators indistinguishable by Peirce pinching

An off-diagonal corner produces two distinct positive operators with the same
pinched image and the same trace. This is a concrete information-loss
obstruction for the completely positive trace-preserving pinching map.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePositiveCollision

open Matrix InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePinchingChannel
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- Two positive Gram operators with opposite off-diagonal parts. -/
def positivePlus (P A : Mat) : Mat :=
  (1 + conePlus P A) * star (1 + conePlus P A)

def positiveMinus (P A : Mat) : Mat :=
  (1 - conePlus P A) * star (1 - conePlus P A)

theorem positivePlus_posSemidef (P A : Mat) : (positivePlus P A).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose (1 + conePlus P A)

theorem positiveMinus_posSemidef (P A : Mat) : (positiveMinus P A).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose (1 - conePlus P A)

theorem positive_pair_same_pinching (P A : Mat) (hP : P * P = P)
    (hPs : star P = P) :
    evenGrade P (positivePlus P A) = evenGrade P (positiveMinus P A) := by
  unfold positivePlus positiveMinus
  simp only [star_add, star_sub, star_one, star_conePlus hPs A]
  unfold evenGrade conePlus coneMinus
  peirce_nf hP

theorem positive_pair_same_trace (P A : Mat) (hP : P * P = P)
    (hPs : star P = P) : Matrix.trace (positivePlus P A) = Matrix.trace (positiveMinus P A) := by
  rw [← pinching_trace P (positivePlus P A) hP hPs,
    ← pinching_trace P (positiveMinus P A) hP hPs, positive_pair_same_pinching P A hP hPs]

theorem positive_pair_upper_blocks (P A : Mat) (hP : P * P = P)
    (hPs : star P = P) :
    P * positivePlus P A * (1 - P) = conePlus P A ∧
    P * positiveMinus P A * (1 - P) = -conePlus P A := by
  constructor <;> simp only [positivePlus, positiveMinus,
    star_add, star_sub, star_one, star_conePlus hPs A] <;>
    unfold conePlus coneMinus <;> peirce_nf hP

theorem positive_pair_ne (P A : Mat) (hP : P * P = P) (hPs : star P = P)
    (hNonzero : conePlus P A ≠ 0) : positivePlus P A ≠ positiveMinus P A := by
  intro hEq
  have hb := congrArg (fun X : Mat => P * X * (1 - P)) hEq
  rcases positive_pair_upper_blocks P A hP hPs with ⟨hp, hm⟩
  rw [hp, hm] at hb
  apply hNonzero
  ext i j
  have hij : conePlus P A i j = -conePlus P A i j := by
    simpa using congrArg (fun M : Mat => M i j) hb
  exact CharZero.eq_neg_self_iff.mp hij

/-- No map can reconstruct every positive matrix from its pinched image. -/
theorem no_positive_recovery (P A : Mat) (hP : P * P = P) (hPs : star P = P)
    (hNonzero : conePlus P A ≠ 0) :
    ¬ ∃ recovery : Mat → Mat, ∀ X : Mat, X.PosSemidef → recovery (evenGrade P X) = X := by
  rintro ⟨recovery, hRecovery⟩
  have hp := hRecovery (positivePlus P A) (positivePlus_posSemidef P A)
  have hm := hRecovery (positiveMinus P A) (positiveMinus_posSemidef P A)
  rw [positive_pair_same_pinching P A hP hPs] at hp
  exact positive_pair_ne P A hP hPs hNonzero (hp.symm.trans hm)

/-- The common trace of the two Gram operators is a strictly positive real. -/
theorem positive_pair_trace_re_pos (P A : Mat) (hP : P * P = P) (hPs : star P = P)
    (hNonzero : conePlus P A ≠ 0) : 0 < (Matrix.trace (positivePlus P A)).re := by
  have hne := positive_pair_ne P A hP hPs hNonzero
  have hp0 : positivePlus P A ≠ 0 := by
    intro hp
    have ht : Matrix.trace (positiveMinus P A) = 0 := by
      rw [← positive_pair_same_trace P A hP hPs, hp, Matrix.trace_zero]
    have hm : positiveMinus P A = 0 := (positiveMinus_posSemidef P A).trace_eq_zero_iff.mp ht
    exact hne (hp.trans hm.symm)
  have ht0 : Matrix.trace (positivePlus P A) ≠ 0 := by
    intro ht
    exact hp0 ((positivePlus_posSemidef P A).trace_eq_zero_iff.mp ht)
  have hn := (positivePlus_posSemidef P A).trace_nonneg
  have hre : 0 ≤ (Matrix.trace (positivePlus P A)).re := (RCLike.nonneg_iff.mp hn).1
  have him : (Matrix.trace (positivePlus P A)).im = 0 := (RCLike.nonneg_iff.mp hn).2
  have hren : (Matrix.trace (positivePlus P A)).re ≠ 0 := by
    intro h
    apply ht0
    apply Complex.ext <;> simp [h, him]
  exact lt_of_le_of_ne hre (Ne.symm hren)

/-- Normalizing the two positive operators produces distinct density matrices
that are indistinguishable by pinching. -/
theorem exists_indistinguishable_densities (P A : Mat) (hP : P * P = P)
    (hPs : star P = P) (hNonzero : conePlus P A ≠ 0) :
    ∃ ρ σ : Mat, ρ.PosSemidef ∧ σ.PosSemidef ∧
      Matrix.trace ρ = 1 ∧ Matrix.trace σ = 1 ∧ ρ ≠ σ ∧
      evenGrade P ρ = evenGrade P σ := by
  let t : ℝ := (Matrix.trace (positivePlus P A)).re
  have ht : 0 < t := positive_pair_trace_re_pos P A hP hPs hNonzero
  have htn : t ≠ 0 := ne_of_gt ht
  have hn := (positivePlus_posSemidef P A).trace_nonneg
  have him : (Matrix.trace (positivePlus P A)).im = 0 := (RCLike.nonneg_iff.mp hn).2
  have htrace : Matrix.trace (positivePlus P A) = (t : ℂ) := by
    apply Complex.ext <;> simp [t, him]
  let ρ : Mat := t⁻¹ • positivePlus P A
  let σ : Mat := t⁻¹ • positiveMinus P A
  have hρ : ρ.PosSemidef := (positivePlus_posSemidef P A).smul (inv_nonneg.mpr ht.le)
  have hσ : σ.PosSemidef := (positiveMinus_posSemidef P A).smul (inv_nonneg.mpr ht.le)
  have htρ : Matrix.trace ρ = 1 := by
    rw [show ρ = t⁻¹ • positivePlus P A from rfl, Matrix.trace_smul, htrace]
    simp [Complex.real_smul, htn]
  have htσ : Matrix.trace σ = 1 := by
    rw [show σ = t⁻¹ • positiveMinus P A from rfl, Matrix.trace_smul,
      ← positive_pair_same_trace P A hP hPs, htrace]
    simp [Complex.real_smul, htn]
  have hdiff : ρ ≠ σ := by
    intro h
    apply positive_pair_ne P A hP hPs hNonzero
    have h' := congrArg (fun X : Mat => t • X) h
    simpa [ρ, σ, smul_smul, htn] using h'
  have hpinch : evenGrade P ρ = evenGrade P σ := by
    change evenGrade P (t⁻¹ • positivePlus P A) = evenGrade P (t⁻¹ • positiveMinus P A)
    simp only [evenGrade, mul_smul_comm, smul_mul_assoc, ← smul_add]
    exact congrArg (fun X : Mat => t⁻¹ • X) (positive_pair_same_pinching P A hP hPs)
  exact ⟨ρ, σ, hρ, hσ, htρ, htσ, hdiff, hpinch⟩

/-- No recovery map can reverse the pinching channel on all density matrices. -/
theorem no_density_recovery (P A : Mat) (hP : P * P = P) (hPs : star P = P)
    (hNonzero : conePlus P A ≠ 0) :
    ¬ ∃ recovery : Mat → Mat, ∀ ρ : Mat, ρ.PosSemidef → Matrix.trace ρ = 1 →
      recovery (evenGrade P ρ) = ρ := by
  obtain ⟨ρ, σ, hρ, hσ, htρ, htσ, hne, heq⟩ :=
    exists_indistinguishable_densities P A hP hPs hNonzero
  rintro ⟨recovery, hRecovery⟩
  have hr := hRecovery ρ hρ htρ
  have hs := hRecovery σ hσ htσ
  rw [heq] at hr
  exact hne (hr.symm.trans hs)

/-- In a full matrix algebra any two nonzero matrices admit a nonzero
intermediate sandwich. The witness is a matrix unit, with no choice of basis
adapted to either matrix. -/
theorem exists_nonzero_matrix_sandwich (U V : Mat) (hU : U ≠ 0) (hV : V ≠ 0) :
    ∃ A : Mat, U * A * V ≠ 0 := by
  have hu : ∃ i j, U i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hU
    ext i j
    exact h i j
  have hv : ∃ i j, V i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hV
    ext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hu
  obtain ⟨k, l, hkl⟩ := hv
  refine ⟨Matrix.single j k 1, ?_⟩
  intro h
  have hentry := congrArg (fun X : Mat => X i l) h
  have hproduct : (U * Matrix.single j k (1 : ℂ) * V) i l = U i j * V k l := by
    rw [mul_assoc, Matrix.mul_apply, Finset.sum_eq_single j]
    · simp
    · intro x _ hx
      simp [Matrix.single_mul_apply_of_ne (1 : ℂ) j k x l hx V]
    · simp
  rw [hproduct] at hentry
  exact (mul_ne_zero hij hkl) (by simpa using hentry)

/-- A nontrivial self-adjoint idempotent on a full finite matrix algebra
cannot be reversed on every density matrix after pinching. -/
theorem nontrivial_pinching_no_density_recovery (P : Mat) (hP : P * P = P)
    (hPs : star P = P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ¬ ∃ recovery : Mat → Mat, ∀ ρ : Mat, ρ.PosSemidef → Matrix.trace ρ = 1 →
      recovery (evenGrade P ρ) = ρ := by
  have hQ : 1 - P ≠ 0 := by
    intro h
    exact hP1 (sub_eq_zero.mp h).symm
  obtain ⟨A, hA⟩ := exists_nonzero_matrix_sandwich P (1 - P) hP0 hQ
  exact no_density_recovery P A hP hPs hA

/-- Universal recovery of density matrices occurs exactly for a trivial
idempotent. This is a characterization for the full matrix algebra. -/
theorem density_recovery_iff_trivial (P : Mat) (hP : P * P = P) (hPs : star P = P) :
    (∃ recovery : Mat → Mat, ∀ ρ : Mat, ρ.PosSemidef → Matrix.trace ρ = 1 →
      recovery (evenGrade P ρ) = ρ) ↔ P = 0 ∨ P = 1 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    exact nontrivial_pinching_no_density_recovery P hP hPs hn.1 hn.2 h
  · rintro (rfl | rfl)
    · refine ⟨id, ?_⟩
      intro ρ _ _
      simp [evenGrade]
    · refine ⟨id, ?_⟩
      intro ρ _ _
      simp [evenGrade]

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeircePositiveCollision

end

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Characteristic polynomial, resolvent, and identity kernel

Dependency order: full matrix algebra → characteristic determinant →
invertible spectral difference → two-sided Green kernel → ordered perturbation.
The determinant is a scalar invariant of a full matrix; its reciprocal alone
is not the resolvent. The adjugate supplies the operator numerator.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CharacteristicResolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

def spectralDifference (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  Matrix.scalar n z - A

def resolvent (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (spectralDifference A z)⁻¹

/-- The full adjugate numerator is essential even though the denominator is
the scalar characteristic polynomial. -/
theorem resolvent_adjugate (A : Matrix n n ℂ) (z : ℂ) :
    resolvent A z = (A.charpoly.eval z)⁻¹ • (spectralDifference A z).adjugate := by
  rw [resolvent, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.eval_charpoly]
  rfl

theorem difference_mul_resolvent (A : Matrix n n ℂ) (z : ℂ)
    (hz : A.charpoly.eval z ≠ 0) : spectralDifference A z * resolvent A z = 1 := by
  apply Matrix.mul_nonsing_inv
  apply isUnit_iff_ne_zero.mpr
  simpa only [Matrix.eval_charpoly, spectralDifference] using hz

theorem resolvent_mul_difference (A : Matrix n n ℂ) (z : ℂ)
    (hz : A.charpoly.eval z ≠ 0) : resolvent A z * spectralDifference A z = 1 := by
  apply Matrix.nonsing_inv_mul
  apply isUnit_iff_ne_zero.mpr
  simpa only [Matrix.eval_charpoly, spectralDifference] using hz

/-- The finite Green kernel reproduces the Kronecker delta. -/
theorem green_kernel_delta (A : Matrix n n ℂ) (z : ℂ)
    (hz : A.charpoly.eval z ≠ 0) (i j : n) :
    ∑ k, spectralDifference A z i k * resolvent A z k j = if i = j then 1 else 0 := by
  have h := congrArg (fun M : Matrix n n ℂ => M i j) (difference_mul_resolvent A z hz)
  simpa only [Matrix.mul_apply, Matrix.one_apply] using h

/-- The resolvent difference keeps the order of two arbitrary input
matrices. There is no hypothesis that A and B commute. -/
theorem resolvent_sub (A B : Matrix n n ℂ) (z : ℂ)
    (hA : A.charpoly.eval z ≠ 0) (hB : B.charpoly.eval z ≠ 0) :
    resolvent A z - resolvent B z =
      resolvent A z * (A - B) * resolvent B z := by
  have hdiff : spectralDifference B z - spectralDifference A z = A - B := by
    unfold spectralDifference
    abel
  rw [← hdiff]
  simp only [mul_sub, sub_mul, mul_assoc]
  rw [difference_mul_resolvent B z hB, mul_one, ← mul_assoc,
    resolvent_mul_difference A z hA, one_mul]

/-- A change of basis transports the full resolvent by conjugation.  The
matrix products retain their order; no commutativity assumption is made on
the operators.  `F` and `G` are inverse matrices, and both spectral
differences are assumed invertible through their characteristic polynomials. -/
theorem resolvent_conjugate
    (A F G : Matrix n n ℂ) (z : ℂ)
    (hFG : F * G = 1) (hGF : G * F = 1)
    (hA : A.charpoly.eval z ≠ 0)
    (hconj : ((F * A) * G).charpoly.eval z ≠ 0) :
    resolvent ((F * A) * G) z = (F * resolvent A z) * G := by
  let D := spectralDifference A z
  let D' := spectralDifference ((F * A) * G) z
  have hscalar : (F * Matrix.scalar n z) * G = Matrix.scalar n z := by
    calc
      (F * Matrix.scalar n z) * G =
          (Matrix.scalar n z * F) * G := by
            rw [(Matrix.scalar_comm z (fun c => by exact mul_comm z c) F).symm]
      _ = Matrix.scalar n z * (F * G) := by rw [mul_assoc]
      _ = Matrix.scalar n z := by rw [hFG, mul_one]
  have hD : D' = (F * D) * G := by
    dsimp [D', D, spectralDifference]
    calc
      Matrix.scalar n z - (F * A) * G =
          ((F * Matrix.scalar n z) * G) - (F * A) * G := by rw [hscalar]
      _ = (F * (Matrix.scalar n z - A)) * G := by
          rw [mul_sub, sub_mul]
  have hright : D' * ((F * resolvent A z) * G) = 1 := by
    rw [hD]
    calc
      ((F * D) * G) * ((F * resolvent A z) * G) =
          (F * (D * (G * F) * resolvent A z)) * G := by
            simp only [mul_assoc]
      _ = (F * (D * resolvent A z)) * G := by rw [hGF, mul_one]
      _ = (F * 1) * G := by
            rw [difference_mul_resolvent A z hA]
      _ = 1 := by simpa using hFG
  calc
    resolvent ((F * A) * G) z =
        resolvent ((F * A) * G) z * 1 := by simp
    _ = resolvent ((F * A) * G) z *
          (D' * ((F * resolvent A z) * G)) := by rw [hright]
    _ = (resolvent ((F * A) * G) z * D') *
          ((F * resolvent A z) * G) := by rw [← mul_assoc]
    _ = 1 * ((F * resolvent A z) * G) := by
          rw [resolvent_mul_difference ((F * A) * G) z hconj]
    _ = (F * resolvent A z) * G := by rw [one_mul]

/-- An operator that anticommutes with A intertwines the two resolvents at
opposite spectral parameters. This is the algebraic parity relation; it
does not identify parity with arithmetic Möbius inversion. -/
theorem parity_resolvent (A Γ : Matrix n n ℂ) (z : ℂ)
    (hodd : Γ * A = -(A * Γ))
    (hz : A.charpoly.eval z ≠ 0) (hnz : A.charpoly.eval (-z) ≠ 0) :
    Γ * resolvent A z = -(resolvent A (-z) * Γ) := by
  have hc : Matrix.scalar n z * Γ = Γ * Matrix.scalar n z :=
    Matrix.scalar_comm z (fun c => by exact mul_comm z c) Γ
  have hd : spectralDifference A (-z) * Γ = -(Γ * spectralDifference A z) := by
    simp only [spectralDifference, map_neg, sub_mul, mul_sub, neg_mul, hodd]
    rw [hc]
    abel
  calc
    Γ * resolvent A z =
        (resolvent A (-z) * spectralDifference A (-z)) * Γ * resolvent A z := by
      rw [resolvent_mul_difference A (-z) hnz, one_mul]
    _ = resolvent A (-z) * (spectralDifference A (-z) * Γ) * resolvent A z := by
      simp only [mul_assoc]
    _ = _ := by
      rw [hd]
      simp only [mul_neg, neg_mul, mul_assoc, difference_mul_resolvent A z hz, mul_one]

end InfoGeometry.OperatorAlgebra.CharacteristicResolvent

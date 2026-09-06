import InfoGeometry.Lie.SplitOctonionRegularMultiplicationSpectralBridge
import InfoGeometry.Physics.HestenesKreinOperatorCalculus

/-!
# Regular multiplication and Hestenes exponential bridge

This file is the analytic consumer of the algebraic regular-multiplication
owner.  The latter only assumes `Ring` and `Algebra`; the exponential layer
adds the explicit normed-algebra and completeness hypotheses required by
`NormedSpace.exp`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionRegularMultiplicationHestenesBridge

open InfoGeometry.Lie.SplitOctonionRegularMultiplicationSpectralBridge
open InfoGeometry.Physics.HestenesKreinOperatorCalculus

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℝ A

/-- A square-root-normalized positive scalar-square generator. -/
theorem exp_of_sq_eq_pos_scalar
    (G : A) (r t : ℝ) (hr : r ≠ 0)
    (hG : G ^ 2 = (r ^ 2) • (1 : A)) :
    NormedSpace.exp (t • G) =
      Real.cosh (r * t) • (1 : A) +
        (Real.sinh (r * t) / r) • G := by
  let H : A := r⁻¹ • G
  have hH : H ^ 2 = (1 : A) := by
    dsimp [H]
    rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
    have hG' : G * G = (r ^ 2) • (1 : A) := by simpa [pow_two] using hG
    rw [hG', smul_smul]
    have hinv : r⁻¹ * r⁻¹ * r ^ 2 = (1 : ℝ) := by
      calc
        r⁻¹ * r⁻¹ * r ^ 2 = (r⁻¹ * r) * (r⁻¹ * r) := by
          rw [pow_two]
          ring
        _ = 1 := by simp [inv_mul_cancel₀ hr]
    rw [hinv]
    simp
  have hexp := exp_of_sq_eq_one H hH (r * t)
  have hscale : (r * t) • H = t • G := by
    dsimp [H]
    rw [smul_smul]
    have hscalar : (r * t) * r⁻¹ = t := by
      field_simp [hr]
    rw [hscalar]
  rw [hscale] at hexp
  have hcoeff : Real.sinh (r * t) • H =
      (Real.sinh (r * t) / r) • G := by
    dsimp [H]
    rw [smul_smul]
    congr 1
  rw [hcoeff] at hexp
  exact hexp

/-- A square-root-normalized negative scalar-square generator. -/
theorem exp_of_sq_eq_neg_scalar
    (G : A) (r t : ℝ) (hr : r ≠ 0)
    (hG : G ^ 2 = -(r ^ 2) • (1 : A)) :
    NormedSpace.exp (t • G) =
      Real.cos (r * t) • (1 : A) +
        (Real.sin (r * t) / r) • G := by
  let H : A := r⁻¹ • G
  have hH : H ^ 2 = -(1 : A) := by
    dsimp [H]
    rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
    have hG' : G * G = -(r ^ 2) • (1 : A) := by simpa [pow_two] using hG
    rw [hG', smul_smul]
    have hinv : r⁻¹ * r⁻¹ * -(r ^ 2) = (-1 : ℝ) := by
      calc
        r⁻¹ * r⁻¹ * -(r ^ 2) = -(r⁻¹ * r⁻¹ * r ^ 2) := by ring
        _ = -1 := by
          rw [show r⁻¹ * r⁻¹ * r ^ 2 = (1 : ℝ) by
            calc
              r⁻¹ * r⁻¹ * r ^ 2 = (r⁻¹ * r) * (r⁻¹ * r) := by
                rw [pow_two]
                ring
              _ = 1 := by simp [inv_mul_cancel₀ hr]]
    rw [hinv]
    exact neg_one_smul ℝ (1 : A)
  have hexp := exp_of_sq_eq_neg_one H hH (r * t)
  have hscale : (r * t) • H = t • G := by
    dsimp [H]
    rw [smul_smul]
    have hscalar : (r * t) * r⁻¹ = t := by
      field_simp [hr]
    rw [hscalar]
  rw [hscale] at hexp
  have hcoeff : Real.sin (r * t) • H =
      (Real.sin (r * t) / r) • G := by
    dsimp [H]
    rw [smul_smul]
    congr 1
  rw [hcoeff] at hexp
  exact hexp

/-- The nilpotent exponential truncates after its linear term. -/
theorem exp_of_sq_eq_zero
    (G : A) (t : ℝ) (hG : G ^ 2 = (0 : A)) :
    NormedSpace.exp (t • G) = (1 : A) + t • G := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' n : ℕ, ((Nat.factorial n : ℕ) : ℝ)⁻¹ •
      (t • G) ^ n) = _
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.range, pow_zero, pow_one, add_comm]
  · intro n hn
    have h2n : 2 ≤ n := by simpa using hn
    have hpow2 : (t • G) ^ 2 = 0 := by
      rw [pow_two, smul_mul_assoc, mul_smul_comm]
      have hG' : G * G = (0 : A) := by simpa [pow_two] using hG
      rw [hG']
      simp
    rw [pow_eq_zero_of_le h2n hpow2, smul_zero]

def centeredElement
    (X : AlternativeQuadraticElement A) : A :=
  X.x - (X.tr / 2) • (1 : A)

omit [CompleteSpace A] in
theorem centeredElement_sq
    (X : AlternativeQuadraticElement A) :
    centeredElement X ^ 2 =
      (discriminant X.tr X.norm / 4) • (1 : A) := by
  have h := four_traceless_sq_eq_discriminant X
  dsimp [centeredElement]
  calc
    (X.x - (X.tr / 2) • (1 : A)) ^ 2 =
        (1 / 4 : ℝ) • ((4 : ℝ) •
          ((X.x - (X.tr / 2) • (1 : A)) ^ 2)) := by
            simp [smul_smul]
    _ = (1 / 4 : ℝ) • ((discriminant X.tr X.norm) • (1 : A)) := by rw [h]
    _ = (discriminant X.tr X.norm / 4) • (1 : A) := by
      rw [smul_smul]
      congr 1
      ring

theorem centeredElement_exp_hyperbolic
    (X : AlternativeQuadraticElement A) (r t : ℝ) (hr : r ≠ 0)
    (hΔ : discriminant X.tr X.norm = 4 * r ^ 2) :
    NormedSpace.exp (t • centeredElement X) =
      Real.cosh (r * t) • (1 : A) +
        (Real.sinh (r * t) / r) • centeredElement X := by
  apply exp_of_sq_eq_pos_scalar (centeredElement X) r t hr
  rw [centeredElement_sq, hΔ]
  congr 1
  ring

theorem centeredElement_exp_elliptic
    (X : AlternativeQuadraticElement A) (r t : ℝ) (hr : r ≠ 0)
    (hΔ : discriminant X.tr X.norm = -(4 * r ^ 2)) :
    NormedSpace.exp (t • centeredElement X) =
      Real.cos (r * t) • (1 : A) +
        (Real.sin (r * t) / r) • centeredElement X := by
  apply exp_of_sq_eq_neg_scalar (centeredElement X) r t hr
  rw [centeredElement_sq, hΔ]
  congr 1
  ring

theorem centeredElement_exp_parabolic
    (X : AlternativeQuadraticElement A) (t : ℝ)
    (hΔ : discriminant X.tr X.norm = 0) :
    NormedSpace.exp (t • centeredElement X) =
      (1 : A) + t • centeredElement X := by
  apply exp_of_sq_eq_zero (centeredElement X) t
  rw [centeredElement_sq, hΔ]
  simp

theorem centeredElement_exp_hyperbolic_of_pos_discriminant
    (X : AlternativeQuadraticElement A) (t : ℝ)
    (hΔ : 0 < discriminant X.tr X.norm) :
    NormedSpace.exp (t • centeredElement X) =
      Real.cosh ((Real.sqrt (discriminant X.tr X.norm) / 2) * t) • (1 : A) +
        (Real.sinh ((Real.sqrt (discriminant X.tr X.norm) / 2) * t) /
          (Real.sqrt (discriminant X.tr X.norm) / 2)) • centeredElement X := by
  let r : ℝ := Real.sqrt (discriminant X.tr X.norm) / 2
  have hr : r ≠ 0 := by
    dsimp [r]
    exact ne_of_gt (div_pos (Real.sqrt_pos.2 hΔ) (by norm_num))
  have hs : (Real.sqrt (discriminant X.tr X.norm)) ^ 2 =
      discriminant X.tr X.norm := Real.sq_sqrt (le_of_lt hΔ)
  have hΔ' : discriminant X.tr X.norm = 4 * r ^ 2 := by
    dsimp [r]
    calc
      discriminant X.tr X.norm = (Real.sqrt (discriminant X.tr X.norm)) ^ 2 := hs.symm
      _ = 4 * (Real.sqrt (discriminant X.tr X.norm) / 2) ^ 2 := by ring
  simpa [r] using centeredElement_exp_hyperbolic X r t hr hΔ'

theorem centeredElement_exp_elliptic_of_neg_discriminant
    (X : AlternativeQuadraticElement A) (t : ℝ)
    (hΔ : discriminant X.tr X.norm < 0) :
    NormedSpace.exp (t • centeredElement X) =
      Real.cos ((Real.sqrt (-discriminant X.tr X.norm) / 2) * t) • (1 : A) +
        (Real.sin ((Real.sqrt (-discriminant X.tr X.norm) / 2) * t) /
          (Real.sqrt (-discriminant X.tr X.norm) / 2)) • centeredElement X := by
  let r : ℝ := Real.sqrt (-discriminant X.tr X.norm) / 2
  have hr : r ≠ 0 := by
    dsimp [r]
    exact ne_of_gt (div_pos (Real.sqrt_pos.2 (neg_pos.mpr hΔ)) (by norm_num))
  have hs : (Real.sqrt (-discriminant X.tr X.norm)) ^ 2 =
      -discriminant X.tr X.norm :=
    Real.sq_sqrt (le_of_lt (neg_pos.mpr hΔ))
  have hΔ' : discriminant X.tr X.norm = -(4 * r ^ 2) := by
    dsimp [r]
    calc
      discriminant X.tr X.norm = -((Real.sqrt (-discriminant X.tr X.norm)) ^ 2) := by
        rw [hs]
        ring
      _ = -(4 * (Real.sqrt (-discriminant X.tr X.norm) / 2) ^ 2) := by ring
  simpa [r] using centeredElement_exp_elliptic X r t hr hΔ'

end InfoGeometry.Lie.SplitOctonionRegularMultiplicationHestenesBridge

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZetaFunctionalEquationDuality

/-!
# Homogeneous completed-xi coordinates and the real split two-lane algebra

The pair `(p,q) = (s,1-s)` is a homogeneous presentation of the marked
projective coordinate `s/(1-s)`.  The functional reflection is the lane swap,
the diagonal scaling is the split-Cartan action, and their product is the
real square-minus-one axis.  This file records only these finite coordinate
identities and the already-owned completed-xi reflection theorem.

No quotient of the zero set, Klein-bottle identification, or Riemann
hypothesis statement is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.CompletedXiHomogeneousHestenesBridge

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.ZetaFunctionalEquationLayer
open InfoGeometry.Canonical.ZetaFunctionalEquationDuality

abbrev HomogeneousPair := ℂ × ℂ

def homogeneousPair (s : ℂ) : HomogeneousPair := (s, 1 - s)

def homogeneousRatio (P : HomogeneousPair) : ℂ := P.1 / P.2

def homogeneousSwap (P : HomogeneousPair) : HomogeneousPair := (P.2, P.1)

def homogeneousEpsilon (P : HomogeneousPair) : HomogeneousPair :=
  (P.1, -P.2)

def homogeneousK (P : HomogeneousPair) : HomogeneousPair :=
  (-P.2, P.1)

def homogeneousScale (a : ℂ) (P : HomogeneousPair) : HomogeneousPair :=
  (a * P.1, a⁻¹ * P.2)

theorem homogeneousScale_one (P : HomogeneousPair) :
    homogeneousScale 1 P = P := by
  cases P
  simp [homogeneousScale]

theorem homogeneousScale_comp (a b : ℂ) (P : HomogeneousPair) :
    homogeneousScale a (homogeneousScale b P) =
      homogeneousScale (a * b) P := by
  cases P
  ext <;> simp [homogeneousScale, mul_assoc] <;> ring

@[simp] theorem homogeneousPair_fst (s : ℂ) :
    (homogeneousPair s).1 = s := rfl

@[simp] theorem homogeneousPair_snd (s : ℂ) :
    (homogeneousPair s).2 = 1 - s := rfl

@[simp] theorem homogeneousSwap_involutive (P : HomogeneousPair) :
    homogeneousSwap (homogeneousSwap P) = P := by
  cases P
  rfl

theorem homogeneousSwap_pair (s : ℂ) :
    homogeneousSwap (homogeneousPair s) = homogeneousPair (1 - s) := by
  simp [homogeneousSwap, homogeneousPair]

theorem homogeneousEpsilon_sq (P : HomogeneousPair) :
    homogeneousEpsilon (homogeneousEpsilon P) = P := by
  cases P
  simp [homogeneousEpsilon]

theorem homogeneousK_sq (P : HomogeneousPair) :
    homogeneousK (homogeneousK P) = (-P.1, -P.2) := by
  cases P
  rfl

theorem homogeneousK_sq_eq_neg (P : HomogeneousPair) :
    homogeneousK (homogeneousK P) = -P := by
  cases P
  rfl

theorem homogeneousSwap_epsilon_swap (P : HomogeneousPair) :
    homogeneousSwap (homogeneousEpsilon (homogeneousSwap P)) =
      -homogeneousEpsilon P := by
  cases P
  simp [homogeneousSwap, homogeneousEpsilon]

theorem homogeneousK_eq_swap_epsilon (P : HomogeneousPair) :
    homogeneousK P = homogeneousSwap (homogeneousEpsilon P) := by
  cases P
  rfl

theorem homogeneousRatio_pair (s : ℂ) :
    homogeneousRatio (homogeneousPair s) = cayleyToFugacity s := rfl

theorem homogeneousRatio_swap
    (P : HomogeneousPair) (hp : P.1 ≠ 0) (hq : P.2 ≠ 0) :
    homogeneousRatio (homogeneousSwap P) =
      (homogeneousRatio P)⁻¹ := by
  unfold homogeneousRatio homogeneousSwap
  field_simp [hp, hq]

theorem homogeneousRatio_pair_reflection (s : ℂ) :
    homogeneousRatio (homogeneousPair (1 - s)) =
      (homogeneousRatio (homogeneousPair s))⁻¹ := by
  simpa [homogeneousRatio_pair] using
    (cayleyToFugacity_one_sub_eq_inv s)

theorem homogeneousRatio_K
    (P : HomogeneousPair) (hp : P.1 ≠ 0) (hq : P.2 ≠ 0) :
    homogeneousRatio (homogeneousK P) =
      -(homogeneousRatio P)⁻¹ := by
  unfold homogeneousK homogeneousRatio
  field_simp [hp, hq]

theorem homogeneousRatio_scale
    (a : ℂ) (P : HomogeneousPair) (ha : a ≠ 0) (hq : P.2 ≠ 0) :
    homogeneousRatio (homogeneousScale a P) =
      a ^ 2 * homogeneousRatio P := by
  unfold homogeneousScale homogeneousRatio
  field_simp [hq, ha]

theorem homogeneousSwap_scale_swap
    (a : ℂ) (P : HomogeneousPair) :
    homogeneousSwap (homogeneousScale a (homogeneousSwap P)) =
      homogeneousScale (a⁻¹) P := by
  cases P
  ext <;> simp [homogeneousSwap, homogeneousScale]

def homogeneousCartanFlow (t : ℝ) (P : HomogeneousPair) : HomogeneousPair :=
  homogeneousScale (Real.exp t : ℂ) P

theorem homogeneousCartanFlow_apply (t : ℝ) (P : HomogeneousPair) :
    homogeneousCartanFlow t P =
      ((Real.exp t : ℂ) * P.1, (Real.exp (-t) : ℂ) * P.2) := by
  unfold homogeneousCartanFlow homogeneousScale
  have h_exp : (Real.exp t : ℂ)⁻¹ = (Real.exp (-t) : ℂ) := by
    rw [← Complex.ofReal_inv, Real.exp_neg]
  rw [h_exp]

theorem homogeneousCartanFlow_zero (P : HomogeneousPair) :
    homogeneousCartanFlow 0 P = P := by
  simp [homogeneousCartanFlow, homogeneousScale]

theorem homogeneousCartanFlow_add (s t : ℝ) (P : HomogeneousPair) :
    homogeneousCartanFlow (s + t) P =
      homogeneousCartanFlow s (homogeneousCartanFlow t P) := by
  unfold homogeneousCartanFlow
  rw [homogeneousScale_comp]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.exp_add]

theorem homogeneousRatio_cartanFlow
    (t : ℝ) (P : HomogeneousPair) (hP : P.2 ≠ 0) :
    homogeneousRatio (homogeneousCartanFlow t P) =
      (Real.exp (2 * t) : ℂ) * homogeneousRatio P := by
  have h_exp : (Real.exp t : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero t
  rw [homogeneousCartanFlow, homogeneousRatio_scale _ P h_exp hP]
  have h_sq : (Real.exp t : ℂ) ^ 2 = (Real.exp (2 * t) : ℂ) := by
    rw [pow_two, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  rw [h_sq]

theorem homogeneousSwap_cartan_conjugacy (t : ℝ) (P : HomogeneousPair) :
    homogeneousSwap (homogeneousCartanFlow t (homogeneousSwap P)) =
      homogeneousCartanFlow (-t) P := by
  rw [homogeneousCartanFlow, homogeneousSwap_scale_swap]
  unfold homogeneousCartanFlow homogeneousScale
  have h_exp : (Real.exp t : ℂ)⁻¹ = (Real.exp (-t) : ℂ) := by
    rw [← Complex.ofReal_inv, Real.exp_neg]
  rw [h_exp]

def homogeneousCompletedXi (P : HomogeneousPair) : ℂ :=
  completedRiemannXi (P.1 / (P.1 + P.2))

theorem homogeneousCompletedXi_swap
    (P : HomogeneousPair) (hsum : P.1 + P.2 ≠ 0) :
    homogeneousCompletedXi P = homogeneousCompletedXi (homogeneousSwap P) := by
  unfold homogeneousCompletedXi homogeneousSwap
  have hreflect :
      1 - P.1 / (P.1 + P.2) = P.2 / (P.1 + P.2) := by
    field_simp [hsum]
    ring
  calc
    completedRiemannXi (P.1 / (P.1 + P.2)) =
        completedRiemannXi (1 - P.1 / (P.1 + P.2)) :=
      completedRiemannXi_reflection _
    _ = completedRiemannXi (P.2 / (P.1 + P.2)) := by rw [hreflect]
    _ = completedRiemannXi (P.2 / (P.2 + P.1)) := by
      rw [add_comm P.1 P.2]

theorem homogeneousCompletedXi_pair (s : ℂ) :
    homogeneousCompletedXi (homogeneousPair s) = completedRiemannXi s := by
  unfold homogeneousCompletedXi homogeneousPair
  have hsum : s + (1 - s) = (1 : ℂ) := by ring
  rw [hsum]
  simp

theorem homogeneousRatio_pair_critical_iff (s : ℂ) :
    OnCriticalLine s ↔
      ‖homogeneousRatio (homogeneousPair s)‖ = 1 := by
  simpa [homogeneousRatio_pair] using
    (criticalLine_iff_cayleyCircle s)

end InfoGeometry.Canonical.CompletedXiHomogeneousHestenesBridge

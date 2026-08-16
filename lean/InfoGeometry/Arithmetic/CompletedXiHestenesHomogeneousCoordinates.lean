import Mathlib.Tactic

import InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge

/-!
# Completed Xi in homogeneous Hestenes coordinates

This file is the small algebraic commuting square behind the completed-Xi
Cayley coordinate.  It uses the distinguished pair `(s, 1 - s)` rather than
introducing an unrelated projective chart.

The file stops before logarithmic branches, cylinder quotients, and Klein
gluing.  It also makes no assertion about the location of zeta zeros.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

abbrev HomogeneousCoord : Type := ℂ × ℂ

/-- The distinguished two-lane homogeneous coordinate of `s`. -/
def homogeneousCoord (s : ℂ) : HomogeneousCoord :=
  (s, 1 - s)

/-- Hestenes/Weyl swap of the two homogeneous lanes. -/
def hestenesSwap : HomogeneousCoord → HomogeneousCoord :=
  fun X => (X.2, X.1)

/-- Split Cartan grading on the homogeneous lanes. -/
def hestenesEpsilon : HomogeneousCoord → HomogeneousCoord :=
  fun X => (X.1, -X.2)

/-- Real quarter-turn axis on the homogeneous lanes. -/
def hestenesK : HomogeneousCoord → HomogeneousCoord :=
  fun X => (-X.2, X.1)

/-- Projective ratio of a homogeneous pair. -/
def projectiveRatio (X : HomogeneousCoord) : ℂ :=
  X.1 / X.2

/-- The zeta projective coordinate `τ = s/(1-s)`. -/
def tau (s : ℂ) : ℂ :=
  projectiveRatio (homogeneousCoord s)

theorem homogeneousCoord_one_sub (s : ℂ) :
    homogeneousCoord (1 - s) =
      hestenesSwap (homogeneousCoord s) := by
  unfold homogeneousCoord hestenesSwap
  congr 1 <;> ring

theorem tau_eq_cayleyToFugacity (s : ℂ) :
    tau s = cayleyToFugacity s :=
  rfl

theorem tau_one_sub_eq_inv (s : ℂ) :
    tau (1 - s) = (tau s)⁻¹ := by
  simpa [tau] using
    (cayleyToFugacity_one_sub_eq_inv s)

/-- Diagonal determinant-one split-Cartan flow on homogeneous coordinates. -/
def cartanFlow (t : ℝ) : HomogeneousCoord → HomogeneousCoord :=
  fun X =>
    ((Real.exp t : ℂ) * X.1,
      (Real.exp (-t) : ℂ) * X.2)

theorem cartanFlow_apply (t : ℝ) (p q : ℂ) :
    cartanFlow t (p, q) =
      ((Real.exp t : ℂ) * p,
        (Real.exp (-t) : ℂ) * q) :=
  rfl

theorem projectiveRatio_cartanFlow
    (t : ℝ) {p q : ℂ} (hq : q ≠ 0) :
    projectiveRatio (cartanFlow t (p, q)) =
      (Real.exp (2 * t) : ℂ) * projectiveRatio (p, q) := by
  unfold projectiveRatio cartanFlow
  field_simp [hq, ne_of_gt (Real.exp_pos t),
    ne_of_gt (Real.exp_pos (-t))]
  have hexp :
      (Real.exp (-t) : ℂ) * (Real.exp (t * 2) : ℂ) =
        (Real.exp t : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    (Real.exp t : ℂ) * p = p * (Real.exp t : ℂ) := by ring
    _ = p * ((Real.exp (-t) : ℂ) * (Real.exp (t * 2) : ℂ)) := by
      rw [hexp]
    _ = p * (Real.exp (-t) : ℂ) * (Real.exp (t * 2) : ℂ) := by
      ring

theorem hestenesSwap_cartanFlow_swap
    (t : ℝ) (X : HomogeneousCoord) :
    hestenesSwap (cartanFlow t (hestenesSwap X)) =
      cartanFlow (-t) X := by
  rcases X with ⟨p, q⟩
  unfold hestenesSwap cartanFlow
  simp [Real.exp_neg]

theorem projectiveRatio_hestenesK
    {p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    projectiveRatio (hestenesK (p, q)) =
      -(projectiveRatio (p, q))⁻¹ := by
  unfold projectiveRatio hestenesK
  field_simp [hp, hq]

theorem criticalLine_iff_tau_unitCircle (s : ℂ) :
    OnCriticalLine s ↔
      OnLeeYangCircle (tau s) := by
  simpa [tau_eq_cayleyToFugacity] using
    (criticalLine_iff_cayley_unitCircle s)

theorem completedXi_functional_equation (s : ℂ) :
    riemannXi (1 - s) = riemannXi s :=
  riemannXi_one_sub s

theorem homogeneous_functional_intertwining (s : ℂ) :
    homogeneousCoord (1 - s) =
      hestenesSwap (homogeneousCoord s) :=
  homogeneousCoord_one_sub s

theorem completedXi_homogeneous_closure (s : ℂ) :
    homogeneousCoord (1 - s) =
        hestenesSwap (homogeneousCoord s) ∧
    tau (1 - s) = (tau s)⁻¹ ∧
    riemannXi (1 - s) = riemannXi s := by
  exact ⟨homogeneous_functional_intertwining s,
    tau_one_sub_eq_inv s,
    completedXi_functional_equation s⟩

end InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates

end

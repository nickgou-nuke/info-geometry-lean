import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HolographicSouriauReconstruction

/-!
# Holographic Tensor-Factor Separation

Finite exact-rational separation theorem for the holographic Souriau layer.

The previous reconstruction module certifies the visible finite witnesses:
`O(5,5)` split metric, Brillouin twist/glide, and rational `sl3` color
generators.  This file upgrades the color-darkness readout to an explicit
tensor-factor statement:

* geometric operators act as `G ⊗ I₃`;
* color operators act as `I₁₀ ⊗ C`;
* these two factors commute for arbitrary rational finite matrices;
* the Brillouin twist/glide remains confined to the geometric factor.

No global bundle, analytic modular uniqueness, or full compact `SU(3)` theorem
is asserted here.  The compact form remains a real-form/socket choice after
complexification; the closed theorem is the rational matrix factorization.
-/

namespace InfoGeometry.Canonical.HolographicTensorFactorSeparation

open scoped Kronecker
open InfoGeometry.Canonical.HolographicSouriauReconstruction

noncomputable section

abbrev Mat6 (R : Type*) := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) R
abbrev Mat30 (R : Type*) := Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) R

/-- Lift a geometric `10 × 10` operator to the geometry-color tensor product. -/
def geomLift10 (G : Mat10 ℚ) : Mat30 ℚ :=
  G ⊗ₖ (1 : Mat3 ℚ)

/-- Lift a color `3 × 3` operator to the geometry-color tensor product. -/
def colorLift10 (C : Mat3 ℚ) : Mat30 ℚ :=
  (1 : Mat10 ℚ) ⊗ₖ C

/-- Lift a Brillouin `2 × 2` geometric operator with the color factor untouched. -/
def geomLift2 (G : Mat2 ℚ) : Mat6 ℚ :=
  G ⊗ₖ (1 : Mat3 ℚ)

/-- Lift a color operator over the Brillouin geometric carrier. -/
def colorLift2 (C : Mat3 ℚ) : Mat6 ℚ :=
  (1 : Mat2 ℚ) ⊗ₖ C

/-- Matrix commutator on an arbitrary square index type. -/
def matCommT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℚ) : Matrix ι ι ℚ :=
  A * B - B * A

/-- Core tensor-factor theorem: geometry and color lifts commute. -/
theorem geom_color_lifts_commute (G : Mat10 ℚ) (C : Mat3 ℚ) :
    geomLift10 G * colorLift10 C = colorLift10 C * geomLift10 G := by
  unfold geomLift10 colorLift10
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- Equivalent commutator-zero form of tensor-factor separation. -/
theorem geom_color_commutator_zero (G : Mat10 ℚ) (C : Mat3 ℚ) :
    matCommT (geomLift10 G) (colorLift10 C) = 0 := by
  simp [matCommT, geom_color_lifts_commute]

/-- `O(5,5)` split metric lift commutes with every displayed color generator. -/
theorem o55Metric_lift_commutes_color (i : Fin 8) :
    matCommT (geomLift10 o55Metric) (colorLift10 (su3ChevalleyGenerator i)) = 0 :=
  geom_color_commutator_zero o55Metric (su3ChevalleyGenerator i)

/-- The split metric remains an involution after tensoring with the color identity. -/
theorem o55Metric_lift_involutive :
    geomLift10 o55Metric * geomLift10 o55Metric = 1 := by
  unfold geomLift10
  rw [← Matrix.mul_kronecker_mul, o55Metric_involutive]
  simp

/-- The Brillouin and color factors commute on the smaller tensor carrier. -/
theorem brillouin_color_lifts_commute (G : Mat2 ℚ) (C : Mat3 ℚ) :
    geomLift2 G * colorLift2 C = colorLift2 C * geomLift2 G := by
  unfold geomLift2 colorLift2
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- The Brillouin twist remains a fermionic square after tensoring with color. -/
theorem brillouinTwist_lift_sq :
    geomLift2 brillouinTwist2 * geomLift2 brillouinTwist2 = -1 := by
  native_decide

/-- The Brillouin glide remains an involution after tensoring with color. -/
theorem brillouinGlide_lift_sq :
    geomLift2 brillouinGlide2 * geomLift2 brillouinGlide2 = 1 := by
  native_decide

/-- The Brillouin twist/glide anticommutation is confined to the geometric factor. -/
theorem brillouin_lift_anticommutes :
    geomLift2 brillouinGlide2 * geomLift2 brillouinTwist2 =
      -geomLift2 brillouinTwist2 * geomLift2 brillouinGlide2 := by
  native_decide

/-- The lifted Brillouin twist commutes with every displayed color generator. -/
theorem brillouinTwist_lift_commutes_color (i : Fin 8) :
    geomLift2 brillouinTwist2 * colorLift2 (su3ChevalleyGenerator i) =
      colorLift2 (su3ChevalleyGenerator i) * geomLift2 brillouinTwist2 :=
  brillouin_color_lifts_commute brillouinTwist2 (su3ChevalleyGenerator i)

/-- The lifted Brillouin glide commutes with every displayed color generator. -/
theorem brillouinGlide_lift_commutes_color (i : Fin 8) :
    geomLift2 brillouinGlide2 * colorLift2 (su3ChevalleyGenerator i) =
      colorLift2 (su3ChevalleyGenerator i) * geomLift2 brillouinGlide2 :=
  brillouin_color_lifts_commute brillouinGlide2 (su3ChevalleyGenerator i)

end

end InfoGeometry.Canonical.HolographicTensorFactorSeparation

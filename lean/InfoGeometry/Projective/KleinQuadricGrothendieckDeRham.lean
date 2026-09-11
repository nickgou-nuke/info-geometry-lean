import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadricMonodromy
import InfoGeometry.Clifford.UniversalCoverLog

/-!
# Klein Quadric / Grothendieck–de Rham Motive Bridge

This file is a lightweight bridge layer that packages the Klein-quadric
multivalued-logarithm picture as explicit, kernel-checked Lean definitions:

* 4-vector split potentials `Q(v) = v0^2 + v1^2 + v2^2 + v3^2`
* the 3-factor Klein-chiral determinant `Q(a) Q(b) Q(a-b)`
* zero-determinant factorization on `ℂ`
* logarithmic 1-form witness (`1 / z`) and monodromy increments
* Tomita-like parallel-transport neutrality on the universal cover

This remains compatible with the existing `KleinQuadricMonodromy` theorems.
-/

namespace InfoGeometry.Projective.KleinQuadric.DeRhamMotive

noncomputable section

open Complex
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Clifford.UniversalCoverLog

/-- 4-vectors used for the chiral causal-cone coordinate model. -/
abbrev FourVectorC : Type := InfoGeometry.Algebra.FiniteSpin.Vec4C

/-- Split quadratic potential on a 4-vector: `v0^2 + v1^2 + v2^2 + v3^2`. -/
noncomputable def splitPotential (v : FourVectorC) : ℂ :=
  v ⟨0, by decide⟩ ^ 2 + v ⟨1, by decide⟩ ^ 2 +
    v ⟨2, by decide⟩ ^ 2 + v ⟨3, by decide⟩ ^ 2

/-- Klein-chiral 3-factor determinant-like potential: `Q(a)Q(b)Q(a-b)`. -/
def chiralDetPotential (a b : FourVectorC) : ℂ :=
  splitPotential a * splitPotential b * splitPotential (a - b)

/-- Zero determinant factorization for the chiral potential. -/
theorem chiralDetPotential_eq_zero_iff
    (a b : FourVectorC) :
    chiralDetPotential a b = 0 ↔
      splitPotential a = 0 ∨ splitPotential b = 0 ∨ splitPotential (a - b) = 0 := by
  unfold chiralDetPotential
  constructor
  · intro h
    have h1 : splitPotential a * splitPotential b = 0 ∨ splitPotential (a - b) = 0 := by
      exact mul_eq_zero.mp h
    cases h1 with
    | inl h2 =>
      rcases mul_eq_zero.mp h2 with hA | hB
      · exact Or.inl hA
      · exact Or.inr <| Or.inl hB
    | inr hC => exact Or.inr <| Or.inr hC
  · rintro (hA | hB | hC)
    · simp [hA]
    · simp [hB]
    · simp [hC]

/-- The logarithmic 1-form witness used in the Grothendieck–de Rham stage. -/
def grothendieck_dlog (z : ℂ) : ℂ := (1 : ℂ) / z

/-- The log-potential as a scalar field. -/
def grothendieckLog (z : ℂ) : ℂ := Complex.log z

/-- Logarithmic derivative on the principal branch away from `0` on the slit plane. -/
theorem grothendieckLog_deriv_log (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt grothendieckLog (1 / z) z := by
  simpa [grothendieckLog] using (Complex.hasDerivAt_log hz)

/-- Negative logarithmic derivative on the principal branch (minus-sign convention). -/
theorem grothendieckLog_deriv_neg_log (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => -grothendieckLog w) (-(1 / z)) z := by
  simpa [grothendieckLog] using (Complex.hasDerivAt_log hz).neg

/-- On a circular contour the `d log` class gives the standard `2πi` winding form. -/
theorem circleIntegral_grothendieck_dlog (R : ℝ) (hR : 0 < R) :
    (∮ z in C((0 : ℂ), R), grothendieck_dlog z) = (2 * Real.pi * Complex.I : ℂ) := by
  unfold grothendieck_dlog
  simpa [InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.poleForm] using
    (InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.circleIntegral_one_div R hR)

/-- The Grothendieck–de Rham class of the `n`-winding log-form around the pole. -/
def grothendieckWindingClass (n : ℤ) : ℂ :=
  (n : ℂ) * (2 * Real.pi * Complex.I : ℂ)

/-- This is the monodromy class used by Wilson-type holonomy. -/
theorem grothendieckWinding_of_sheet (n : ℤ) :
    Complex.exp (grothendieckWindingClass n) = (1 : ℂ) := by
  simpa [grothendieckWindingClass] using (Complex.exp_int_mul_two_pi_mul_I n)

/-- Universal-cover log monodromy is exactly one sheet jump of `2πi`. -/
theorem tomita_sheet_transport (z : ℂ) (n : ℤ) :
    uLog (z, n + 1) - uLog (z, n) = 2 * Real.pi * Complex.I := by
  change uLog (deckUp (z, n)) - uLog (z, n) = 2 * Real.pi * Complex.I
  rw [uLog_deck_up (z := z) (n := n)]
  ring

/-- Pulling the monodromy increment back to the Klein potential cycle.
This is a formal stepping-stone axiomatisation:
sheet windings act by a pure `2πi` phase and therefore have trivial Wilson holonomy.
-/
theorem grothendieckTomitaWilsonBridge (n : ℤ) (R : ℝ) (hR : 0 < R) :
    Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), R), grothendieck_dlog z)) = (1 : ℂ) := by
  rw [circleIntegral_grothendieck_dlog R hR]
  simpa [grothendieckWindingClass, mul_comm, mul_left_comm, mul_assoc] using
    (Complex.exp_int_mul_two_pi_mul_I n)

end

end InfoGeometry.Projective.KleinQuadric.DeRhamMotive

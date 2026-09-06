import Mathlib.Tactic
import InfoGeometry.Projective.KleinQuadricMonodromy
import InfoGeometry.Clifford.UniversalCoverLog

/-!
# Klein Quadric / Grothendieck–de Rham Motive Bridge

This file is a lightweight bridge layer that packages the Klein-quadric
multivalued-logarithm picture as explicit, kernel-checked Lean definitions:

* 4-vector split potentials `Q(v) = v0^2 + v1^2 + v2^2 + v3^2`
* the 3-factor Klein-chiral determinant `Q(a) Q(b) Q(a-b)`
* zero-determinant factorization on `ℂ`
* logarithmic 1-form property (`1 / z`) and monodromy increments
* Tomita-like parallel-transport neutrality on the universal cover

This remains compatible with the existing `KleinQuadricMonodromy` theorems.
-/

namespace InfoGeometry.Projective.KleinQuadric.DeRhamMotive

noncomputable section

open Complex
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Clifford.UniversalCoverLog

/-- 4-vectors used for the chiral causal-cone coordinate model. -/
abbrev FourVectorC : Type := Fin 4 → ℂ

/-- Split quadratic potential on a 4-vector: `v0^2 + v1^2 + v2^2 + v3^2`. -/
noncomputable def splitPotential (v : FourVectorC) : ℂ :=
  v ⟨0, by decide⟩ ^ 2 + v ⟨1, by decide⟩ ^ 2 +
    v ⟨2, by decide⟩ ^ 2 + v ⟨3, by decide⟩ ^ 2

theorem splitPotential_scale (c : ℂ) (v : FourVectorC) :
    splitPotential (c • v) = c ^ 2 * splitPotential v := by
  simp only [splitPotential, Pi.smul_apply, smul_eq_mul]
  ring

/-- Klein-chiral 3-factor determinant-like potential: `Q(a)Q(b)Q(a-b)`. -/
def chiralDetPotential (a b : FourVectorC) : ℂ :=
  splitPotential a * splitPotential b * splitPotential (a - b)

theorem chiralDetPotential_scale (c : ℂ) (a b : FourVectorC) :
    chiralDetPotential (c • a) (c • b) =
      c ^ 6 * chiralDetPotential a b := by
  unfold chiralDetPotential
  rw [splitPotential_scale, splitPotential_scale]
  have hab : c • a - c • b = c • (a - b) := by
    exact (smul_sub c a b).symm
  rw [hab, splitPotential_scale]
  ring

theorem splitPotential_scale_eq_zero_iff
    (c : ℂ) (hc : c ≠ 0) (v : FourVectorC) :
    splitPotential (c • v) = 0 ↔ splitPotential v = 0 := by
  rw [splitPotential_scale]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hc)
  · intro h
    rw [h, mul_zero]

theorem chiralDetPotential_scale_eq_zero_iff
    (c : ℂ) (hc : c ≠ 0) (a b : FourVectorC) :
    chiralDetPotential (c • a) (c • b) = 0 ↔
      chiralDetPotential a b = 0 := by
  rw [chiralDetPotential_scale]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 6 hc)
  · intro h
    rw [h, mul_zero]

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

/-- The logarithmic 1-form property used in the Grothendieck–de Rham stage. -/
def grothendieck_dlog (z : ℂ) : ℂ := (1 : ℂ) / z

/-- The log-potential as a scalar field. -/
def grothendieckLog (z : ℂ) : ℂ := Complex.log z

/-- The logarithmic one-form is invariant under pullback by a constant
nonzero complex scaling.  This is the algebraic `d log` covariance behind
projective rescaling of Klein coordinates. -/
theorem grothendieck_dlog_pullback_scale
    (c z : ℂ) (hc : c ≠ 0) (hz : z ≠ 0) :
    c * grothendieck_dlog (c * z) = grothendieck_dlog z := by
  unfold grothendieck_dlog
  field_simp

/-- Projective scaling preserves a Klein-null Plücker point while the same
constant scaling leaves the logarithmic one-form pullback unchanged. -/
theorem klein_projective_dlog_scale_compatibility
    (c : ℂ) (hc : c ≠ 0)
    (P : Plucker6 (R := ℂ)) (hP : Plucker6.IsKlein P)
    (z : ℂ) (hz : z ≠ 0) :
    Plucker6.IsKlein (Plucker6.scale c P) ∧
      c * grothendieck_dlog (c * z) = grothendieck_dlog z := by
  exact ⟨Plucker6.isKlein_scale_of c P hP,
    grothendieck_dlog_pullback_scale c z hc hz⟩

/-- Logarithmic derivative on the principal branch away from `0` on the slit plane. -/
theorem grothendieckLog_deriv_log (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt grothendieckLog (1 / z) z := by
  simpa [grothendieckLog] using (Complex.hasDerivAt_log hz)

/-- Negative logarithmic derivative on the principal branch (minus-sign convention). -/
theorem grothendieckLog_deriv_neg_log (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => -grothendieckLog w) (-(1 / z)) z := by
  simpa [grothendieckLog] using (Complex.hasDerivAt_log hz).neg

/-! The local pullback theorem for the logarithmic form.  This is the
    coefficient-level form of `Q^*(dz / z)` and does not introduce a
    manifold differential-form carrier. -/

theorem grothendieckLog_deriv_comp
    {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z)
    (hbranch : f z ∈ Complex.slitPlane) :
    HasDerivAt (fun w => grothendieckLog (f w)) (f' / f z) z := by
  have hlog := (Complex.hasDerivAt_log hbranch).comp z hf
  simpa [grothendieckLog, Function.comp_def, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hlog

/-! ## Native logarithmic product rule -/

/-- The derivative of a logarithm of a product, on the chosen logarithm
branch, is the logarithmic derivative of that product.  The slit-plane
property is kept explicit because no global branch of `Complex.log` exists
on `ℂˣ`. -/
theorem grothendieckLog_deriv_mul
    {f g : ℂ → ℂ} {f' g' z : ℂ}
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z)
    (hfg : f z * g z ∈ Complex.slitPlane) :
    HasDerivAt (fun w => grothendieckLog (f w * g w))
      ((f' * g z + f z * g') / (f z * g z)) z := by
  have hmul := hf.mul hg
  have hlog := (Complex.hasDerivAt_log hfg).comp z hmul
  simpa [grothendieckLog, Function.comp_def, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hlog

/-- Algebraic splitting of the product logarithmic derivative. -/
theorem grothendieckLog_deriv_mul_eq_add
    {f g : ℂ → ℂ} {f' g' z : ℂ}
    (hf : f z ≠ 0) (hg : g z ≠ 0) :
    (f' * g z + f z * g') / (f z * g z) =
      f' / f z + g' / g z := by
  field_simp

/-- On a circular contour the `d log` class gives the standard `2πi` winding form. -/
theorem circleIntegral_grothendieck_dlog (R : ℝ) (hR : 0 < R) :
    (∮ z in C((0 : ℂ), R), grothendieck_dlog z) = (2 * Real.pi * Complex.I : ℂ) := by
  unfold grothendieck_dlog
  simpa [InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.poleForm] using
    (InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.circleIntegral_one_div R hR)

/-- The Grothendieck–de Rham class of the `n`-winding log-form around the pole. -/
def grothendieckWindingClass (n : ℤ) : ℂ :=
  (n : ℂ) * (2 * Real.pi * Complex.I : ℂ)

@[simp] theorem grothendieckWindingClass_zero :
    grothendieckWindingClass 0 = 0 := by
  simp [grothendieckWindingClass]

theorem grothendieckWindingClass_add (m n : ℤ) :
    grothendieckWindingClass (m + n) =
      grothendieckWindingClass m + grothendieckWindingClass n := by
  unfold grothendieckWindingClass
  push_cast
  ring

theorem grothendieckWindingClass_neg (n : ℤ) :
    grothendieckWindingClass (-n) =
      -grothendieckWindingClass n := by
  unfold grothendieckWindingClass
  push_cast
  ring

/-- The de Rham period computes the named Grothendieck winding class. -/
theorem grothendieckWindingClass_eq_circleIntegral
    (n : ℤ) (R : ℝ) (hR : 0 < R) :
    (n : ℂ) * (∮ z in C((0 : ℂ), R), grothendieck_dlog z) =
      grothendieckWindingClass n := by
  rw [circleIntegral_grothendieck_dlog R hR]
  rfl

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

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionRegularProjectors
import InfoGeometry.Canonical.SplitOctonionHyperbolicSpectralProjectors

/-!
# Functional calculus for the split-octonion hyperbolic axis

The projector and exponential identities live in
`SplitOctonionRegularProjectors`.  This file adds the resolvent identity for
that same operator, without introducing an inverse or a second operator
construction.
-/

noncomputable section

namespace SplitOctonion

open scoped BigOperators

def hyperbolicResolventCandidate (g : H) (z : ℝ) :
    Module.End ℝ SplitOctonion :=
  ((z - 1)⁻¹) • hyperbolicProjectorPlus g +
    ((z + 1)⁻¹) • hyperbolicProjectorMinus g

theorem hyperbolicResolventCandidate_left (g : H)
    (hg : Quaternion.normSq g = 1) (z : ℝ)
    (hz_one : z - 1 ≠ 0) (hz_neg_one : z + 1 ≠ 0) :
    ((z • (1 : Module.End ℝ SplitOctonion)) - hyperbolicAxisOperator g).comp
        (hyperbolicResolventCandidate g z) =
      (1 : Module.End ℝ SplitOctonion) := by
  apply LinearMap.ext
  intro x
  have hp := LinearMap.congr_fun
    (hyperbolicAxisOperator_comp_projectorPlus g hg) x
  have hm := LinearMap.congr_fun
    (hyperbolicAxisOperator_comp_projectorMinus g hg) x
  have hp' : hyperbolicAxisOperator g (hyperbolicProjectorPlus g x) =
      hyperbolicProjectorPlus g x := by
    simpa [LinearMap.comp_apply] using hp
  have hm' : hyperbolicAxisOperator g (hyperbolicProjectorMinus g x) =
      -hyperbolicProjectorMinus g x := by
    simpa [LinearMap.comp_apply] using hm
  have hsum := LinearMap.congr_fun
    (hyperbolicProjectorPlus_add_minus g) x
  change z • (((z - 1)⁻¹) • hyperbolicProjectorPlus g x +
      ((z + 1)⁻¹) • hyperbolicProjectorMinus g x) -
    hyperbolicAxisOperator g
      (((z - 1)⁻¹) • hyperbolicProjectorPlus g x +
        ((z + 1)⁻¹) • hyperbolicProjectorMinus g x) = x
  rw [map_add, map_smul, map_smul, hp', hm']
  have ha : z * (z - 1)⁻¹ - (z - 1)⁻¹ = (1 : ℝ) := by
    field_simp [hz_one]
  have hb : z * (z + 1)⁻¹ + (z + 1)⁻¹ = (1 : ℝ) := by
    field_simp [hz_neg_one]
  calc
    z • ((z - 1)⁻¹ • hyperbolicProjectorPlus g x +
        (z + 1)⁻¹ • hyperbolicProjectorMinus g x) -
        ((z - 1)⁻¹ • hyperbolicProjectorPlus g x +
          (z + 1)⁻¹ • -hyperbolicProjectorMinus g x) =
      (z * (z - 1)⁻¹ - (z - 1)⁻¹) • hyperbolicProjectorPlus g x +
        (z * (z + 1)⁻¹ + (z + 1)⁻¹) • hyperbolicProjectorMinus g x := by
          module
    _ = hyperbolicProjectorPlus g x + hyperbolicProjectorMinus g x := by
      rw [ha, hb]
      simp
    _ = x := by simpa using hsum

theorem hyperbolicResolventCandidate_right (g : H)
    (hg : Quaternion.normSq g = 1) (z : ℝ)
    (hz_one : z - 1 ≠ 0) (hz_neg_one : z + 1 ≠ 0) :
    (hyperbolicResolventCandidate g z).comp
        ((z • (1 : Module.End ℝ SplitOctonion)) - hyperbolicAxisOperator g) =
      (1 : Module.End ℝ SplitOctonion) := by
  apply LinearMap.ext
  intro x
  have hsq := LinearMap.congr_fun (hyperbolicAxisOperator_sq g hg) x
  have hsq' : hyperbolicAxisOperator g (hyperbolicAxisOperator g x) = x := by
    simpa [LinearMap.comp_apply] using hsq
  have hp : hyperbolicProjectorPlus g (hyperbolicAxisOperator g x) =
      hyperbolicProjectorPlus g x := by
    change (1 / 2 : ℝ) •
      (hyperbolicAxisOperator g x +
        hyperbolicAxisOperator g (hyperbolicAxisOperator g x)) =
      (1 / 2 : ℝ) • (x + hyperbolicAxisOperator g x)
    rw [hsq']
    rw [add_comm]
  have hm : hyperbolicProjectorMinus g (hyperbolicAxisOperator g x) =
      -hyperbolicProjectorMinus g x := by
    change (1 / 2 : ℝ) •
      (hyperbolicAxisOperator g x -
        hyperbolicAxisOperator g (hyperbolicAxisOperator g x)) =
      -((1 / 2 : ℝ) • (x - hyperbolicAxisOperator g x))
    rw [hsq']
    module
  have hsum := LinearMap.congr_fun
    (hyperbolicProjectorPlus_add_minus g) x
  change ((z - 1)⁻¹) • hyperbolicProjectorPlus g
      (z • x - hyperbolicAxisOperator g x) +
    ((z + 1)⁻¹) • hyperbolicProjectorMinus g
      (z • x - hyperbolicAxisOperator g x) = x
  rw [map_sub, map_sub, map_smul, map_smul, hp, hm]
  have ha : (z - 1)⁻¹ * z - (z - 1)⁻¹ = (1 : ℝ) := by
    field_simp [hz_one]
  have hb : (z + 1)⁻¹ * z + (z + 1)⁻¹ = (1 : ℝ) := by
    field_simp [hz_neg_one]
  calc
    (z - 1)⁻¹ • (z • hyperbolicProjectorPlus g x -
        hyperbolicProjectorPlus g x) +
        (z + 1)⁻¹ • (z • hyperbolicProjectorMinus g x -
          -hyperbolicProjectorMinus g x) =
      ((z - 1)⁻¹ * z - (z - 1)⁻¹) • hyperbolicProjectorPlus g x +
        ((z + 1)⁻¹ * z + (z + 1)⁻¹) • hyperbolicProjectorMinus g x := by
          module
    _ = hyperbolicProjectorPlus g x + hyperbolicProjectorMinus g x := by
      rw [ha, hb]
      simp
    _ = x := by simpa using hsum

/--
The positive-norm polar decomposition in the two reciprocal hyperbolic
spectral sheets.  The quaternionic frame and rapidity are inherited from
`polar_decomposition`; only the exponential factor is rewritten using the
already proved spectral-projector identity.
-/
theorem polar_decomposition_projector (X : SplitOctonion)
    (h : isHyperbolic X) (hb : X.b ≠ 0) :
    X =
      ⟨polarRho X h • polarU X (a_ne_zero_of_isHyperbolic X h), 0⟩ *
        (Real.exp (polarEta X h) •
            hyperbolicProjPlus (polarG X (a_ne_zero_of_isHyperbolic X h) hb) +
          Real.exp (-(polarEta X h)) •
            hyperbolicProjMinus (polarG X (a_ne_zero_of_isHyperbolic X h) hb)) := by
  let ha : X.a ≠ 0 := a_ne_zero_of_isHyperbolic X h
  let g : H := polarG X ha hb
  calc
    X = ⟨polarRho X h • polarU X ha, 0⟩ *
        expHyperbolic 1 (polarEta X h) (J_g g) := by
      simpa [ha, g] using polar_decomposition X h hb
    _ = ⟨polarRho X h • polarU X ha, 0⟩ *
        (Real.exp (polarEta X h) • hyperbolicProjPlus g +
          Real.exp (-(polarEta X h)) • hyperbolicProjMinus g) := by
      rw [expHyperbolic_projector_decomposition g (normSq_polarG X ha hb)]
    _ = ⟨polarRho X h • polarU X (a_ne_zero_of_isHyperbolic X h), 0⟩ *
        (Real.exp (polarEta X h) •
            hyperbolicProjPlus (polarG X (a_ne_zero_of_isHyperbolic X h) hb) +
          Real.exp (-(polarEta X h)) •
            hyperbolicProjMinus (polarG X (a_ne_zero_of_isHyperbolic X h) hb)) := by
      rfl

end SplitOctonion

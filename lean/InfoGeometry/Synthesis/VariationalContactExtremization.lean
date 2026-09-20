import InfoGeometry.Synthesis.QuadraticContactDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Two-variable quadratic contact extremization

The dependency order is scalar derivatives → Fréchet differential → stationary
point; independently, the sum-of-squares identity → strict global minimality.
The action has a minimum, not a hyperbolic saddle. These statements concern the
specified quadratic functions, not the spectrum of an unspecified operator.
-/

noncomputable section

namespace InfoGeometry.Synthesis.VariationalContactExtremization

open ImpedanceMatchingDuality QuadraticContactDerivatives

def contactAction (coupling : ℝ) (point : ℝ × ℝ) : ℝ :=
  action coupling point.1 point.2

def contactDifferential (coupling : ℝ) (point : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (2 * coupling ^ 2 * point.1 - coupling) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (2 * point.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem contactAction_hasFDerivAt (coupling : ℝ) (point : ℝ × ℝ) :
    HasFDerivAt (contactAction coupling) (contactDifferential coupling point) point := by
  have hcapacity := (capacity_hasDerivAt coupling point.1).hasFDerivAt.comp point
    (hasFDerivAt_fst (𝕜 := ℝ) (p := point))
  have hcritical := (criticalValue_hasDerivAt point.2).hasFDerivAt.comp point
    (hasFDerivAt_snd (𝕜 := ℝ) (p := point))
  have hdifferential :
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * point.2)).comp
          (ContinuousLinearMap.snd ℝ ℝ ℝ) -
        (ContinuousLinearMap.toSpanSingleton ℝ (coupling - 2 * coupling ^ 2 * point.1)).comp
          (ContinuousLinearMap.fst ℝ ℝ ℝ) = contactDifferential coupling point := by
    apply ContinuousLinearMap.ext
    intro direction
    change direction.2 * (2 * point.2) -
      direction.1 * (coupling - 2 * coupling ^ 2 * point.1) =
      (2 * coupling ^ 2 * point.1 - coupling) * direction.1 + (2 * point.2) * direction.2
    ring
  have hderivative := hcritical.sub hcapacity
  rw [hdifferential] at hderivative
  exact hderivative

theorem contactDifferential_eq_zero_iff (coupling : ℝ) (point : ℝ × ℝ)
    (hnonzero : coupling ≠ 0) :
    contactDifferential coupling point = 0 ↔ point = (1 / (2 * coupling), 0) := by
  constructor
  · intro hzero
    have hfirst := congrArg (fun differential : (ℝ × ℝ) →L[ℝ] ℝ =>
      differential (1, 0)) hzero
    have hsecond := congrArg (fun differential : (ℝ × ℝ) →L[ℝ] ℝ =>
      differential (0, 1)) hzero
    simp [contactDifferential] at hfirst hsecond
    have hstationary : deriv (fisher_capacity coupling) point.1 = 0 := by
      rw [capacity_deriv]
      linarith
    apply Prod.ext
    · exact (stationary_capacity_iff coupling point.1 hnonzero).mp hstationary
    · simpa using hsecond
  · rintro rfl
    have hcoefficient : 2 * coupling ^ 2 * (1 / (2 * coupling)) - coupling = 0 := by
      field_simp
      ring
    unfold contactDifferential
    dsimp only
    rw [hcoefficient]
    simp

theorem contactAction_zero_at_vertex (coupling : ℝ) (hnonzero : coupling ≠ 0) :
    contactAction coupling (1 / (2 * coupling), 0) = 0 :=
  (action_zero_iff coupling _ _ hnonzero).mpr ⟨rfl, rfl⟩

theorem contactAction_strict_global_minimum (coupling : ℝ) (hnonzero : coupling ≠ 0)
    (point : ℝ × ℝ) (haway : point ≠ (1 / (2 * coupling), 0)) :
    contactAction coupling (1 / (2 * coupling), 0) < contactAction coupling point := by
  rw [contactAction_zero_at_vertex coupling hnonzero]
  apply action_strict_minimum coupling point.1 point.2 hnonzero
  intro hcoordinates
  exact haway (Prod.ext hcoordinates.1 hcoordinates.2)

end InfoGeometry.Synthesis.VariationalContactExtremization

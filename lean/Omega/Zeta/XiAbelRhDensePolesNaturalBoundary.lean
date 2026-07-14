import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The unit circle in the Abel variable. -/
def xi_abel_rh_dense_poles_natural_boundary_unitCircle : Set ℂ :=
  {z : ℂ | ‖z‖ = 1}

/-- Density of the Abel-Weil pole set on the unit circle. -/
def xi_abel_rh_dense_poles_natural_boundary_densePoles
    (poleSet : Set ℂ) : Prop :=
  ∀ ζ ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle, ∀ ε : ℝ, 0 < ε →
    ∃ r ∈ poleSet,
      r ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle ∧ dist r ζ < ε

/-- The no-cancellation hypothesis: every modeled boundary pole is non-removable. -/
def xi_abel_rh_dense_poles_natural_boundary_noCancellation
    (poleSet nonremovableSingularities : Set ℂ) : Prop :=
  ∀ r ∈ poleSet, r ∈ nonremovableSingularities

/-- Any analytic continuation across a boundary point removes singularities on some boundary
arc around that point. -/
def xi_abel_rh_dense_poles_natural_boundary_continuationClearsArc
    (nonremovableSingularities : Set ℂ) (analyticContinuationAcross : ℂ → Prop) : Prop :=
  ∀ ζ ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle,
    analyticContinuationAcross ζ →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ r ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle, dist r ζ < ε →
          r ∉ nonremovableSingularities

/-- The unit circle is a natural boundary: no boundary point admits analytic continuation
across it. -/
def xi_abel_rh_dense_poles_natural_boundary_naturalBoundary
    (analyticContinuationAcross : ℂ → Prop) : Prop :=
  ∀ ζ ∈ xi_abel_rh_dense_poles_natural_boundary_unitCircle,
    ¬ analyticContinuationAcross ζ

/-- Concrete theorem statement for `thm:xi-abel-rh-dense-poles-natural-boundary`. -/
def xi_abel_rh_dense_poles_natural_boundary_statement
    (poleSet nonremovableSingularities : Set ℂ) (analyticContinuationAcross : ℂ → Prop) : Prop :=
  xi_abel_rh_dense_poles_natural_boundary_densePoles poleSet →
    xi_abel_rh_dense_poles_natural_boundary_noCancellation poleSet nonremovableSingularities →
      xi_abel_rh_dense_poles_natural_boundary_continuationClearsArc
        nonremovableSingularities analyticContinuationAcross →
        xi_abel_rh_dense_poles_natural_boundary_naturalBoundary analyticContinuationAcross

/-- Paper label: `thm:xi-abel-rh-dense-poles-natural-boundary`. -/
theorem paper_xi_abel_rh_dense_poles_natural_boundary
    (poleSet nonremovableSingularities : Set ℂ) (analyticContinuationAcross : ℂ → Prop) :
    xi_abel_rh_dense_poles_natural_boundary_statement
      poleSet nonremovableSingularities analyticContinuationAcross := by
  intro hdense hnocancel hclear ζ hζ hcont
  rcases hclear ζ hζ hcont with ⟨ε, hε, hregular⟩
  rcases hdense ζ hζ ε hε with ⟨r, hr_pole, hr_circle, hr_dist⟩
  exact hregular r hr_circle hr_dist (hnocancel r hr_pole)

end Omega.Zeta

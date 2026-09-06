import InfoGeometry.Canonical.InformationPartitionCore
import InfoGeometry.Canonical.DeRhamCantorCohomology
import InfoGeometry.Projective.KleinQuadricGrothendieckDeRham

/-!
# Log-generating potentials, monodromy, and Cantor cohomology

This file is a narrow compatibility bridge.  It combines three existing
kernel-checked readouts without identifying their carriers:

* the scalar derivative of `log Z(τ)` at `τ = 0`;
* the `2πi` logarithmic winding class and its trivial exponential holonomy;
* the algebraic Cantor boundary complex, whose first cohomology is trivial.

No smooth de Rham complex, Haar theorem, Hausdorff measure, or unbounded
operator functional calculus is asserted here.
-/

namespace InfoGeometry.Canonical.LogGeneratingMonodromyCohomology

open InfoGeometry.Canonical.InformationCalculus
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData
open InfoGeometry.Canonical.DeRhamCantorCohomology
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive

noncomputable section

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Log-generating differential and its operator readout -/

/-- The log-generating potential associated with a modular observable. -/
noncomputable def logGeneratingPotential
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) : ℝ → ℝ :=
  fun τ => logInformationPartitionFunction ω K τ

/-- The operator whose scalar readout is the first log-generating differential. -/
noncomputable def logGeneratingOperatorDifferential (K : EndH E) : EndH E := K

theorem logGeneratingPotential_derivative_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E)
    (hω1 : ω (1 : EndH E) = 1) :
    HasDerivAt (logGeneratingPotential ω K) (ω K) 0 := by
  simpa [logGeneratingPotential] using
    (hasDerivAt_logInformationPartitionFunction_zero_of_normalized
      (ω := ω) (K := K) hω1)

theorem logGeneratingPotential_derivative_eq_operator_readout
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E)
    (hω1 : ω (1 : EndH E) = 1) :
    deriv (logGeneratingPotential ω K) 0 =
      ω (logGeneratingOperatorDifferential K) := by
  simpa [logGeneratingOperatorDifferential] using
    (logGeneratingPotential_derivative_zero (ω := ω) (K := K) hω1).deriv

/-! ## Logarithmic monodromy readout -/

/-- The monodromy period of the log-generating branch at winding `n`. -/
def logGeneratingMonodromy (n : ℤ) : ℂ :=
  grothendieckWindingClass n

theorem logGeneratingMonodromy_add (m n : ℤ) :
    logGeneratingMonodromy (m + n) =
      logGeneratingMonodromy m + logGeneratingMonodromy n := by
  exact grothendieckWindingClass_add m n

theorem logGeneratingMonodromy_holonomy_trivial (n : ℤ) :
    Complex.exp (logGeneratingMonodromy n) = (1 : ℂ) := by
  exact grothendieckWinding_of_sheet n

theorem logGeneratingMonodromy_period
    (n : ℤ) (R : ℝ) (hR : 0 < R) :
    logGeneratingMonodromy n =
      (n : ℂ) * (∮ z in C((0 : ℂ), R), grothendieck_dlog z) := by
  symm
  exact grothendieckWindingClass_eq_circleIntegral n R hR

/-! ## Cohomological readout on the binary boundary -/

theorem closed_boundary_log_generating_differential_is_exact
    (f : (ℕ → Bool) → ℂ) (hf : IsClosed f) :
    IsExact f := by
  exact cantor_de_rham_trivial f hf

theorem boundary_log_generating_cohomology_trivial
    (x : DeRhamH1) : x = 0 := by
  exact deRhamH1_subsingleton x

end

end InfoGeometry.Canonical.LogGeneratingMonodromyCohomology

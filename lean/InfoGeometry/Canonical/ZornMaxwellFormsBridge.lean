import InfoGeometry.Canonical.ZornDifferentialFormsLaplacianBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Maxwell equations on the finite differential-form carrier

The homogeneous Maxwell equation is derived from `F = d A` and `d² = 0`.
The sourced equation is kept as an explicit readout hypothesis: it is not a
consequence of the differential alone.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornMaxwellFormsBridge

open ExteriorAlgebra
open ZornDifferentialFormsLaplacianBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def fieldStrength
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential : ExteriorAlgebra R V) : ExteriorAlgebra R V :=
  D.differential potential

def gaugeTransformedPotential
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential gauge : ExteriorAlgebra R V) : ExteriorAlgebra R V :=
  potential + D.differential gauge

theorem gaugeTransformedPotential_fieldStrength
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential gauge : ExteriorAlgebra R V) :
    fieldStrength D (gaugeTransformedPotential D potential gauge) =
      fieldStrength D potential := by
  dsimp [fieldStrength, gaugeTransformedPotential]
  rw [map_add]
  have hg : D.differential (D.differential gauge) = 0 := by
    have h := congrArg
      (fun f : Module.End R (ExteriorAlgebra R V) => f gauge)
      D.differential_sq
    simpa [LinearMap.comp_apply] using h
  rw [hg, add_zero]

theorem fieldStrength_closed
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential : ExteriorAlgebra R V) :
    D.differential (fieldStrength D potential) = 0 := by
  have h := congrArg
    (fun f : Module.End R (ExteriorAlgebra R V) => f potential)
    D.differential_sq
  simpa [fieldStrength, LinearMap.comp_apply] using h

theorem maxwell_homogeneous_equation
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential : ExteriorAlgebra R V) :
    D.differential (fieldStrength D potential) = 0 :=
  fieldStrength_closed D potential

theorem maxwell_sourced_equation
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential current : ExteriorAlgebra R V)
    (hsource : D.codifferential (fieldStrength D potential) = current) :
    D.codifferential (fieldStrength D potential) = current :=
  hsource

theorem maxwell_sourced_gauge_invariant
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential gauge current : ExteriorAlgebra R V)
    (hsource : D.codifferential (fieldStrength D potential) = current) :
    D.codifferential
        (fieldStrength D (gaugeTransformedPotential D potential gauge)) = current := by
  rw [gaugeTransformedPotential_fieldStrength]
  exact hsource

theorem maxwell_form_equations
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential current : ExteriorAlgebra R V)
    (hsource : D.codifferential (fieldStrength D potential) = current) :
    D.differential (fieldStrength D potential) = 0 ∧
      D.codifferential (fieldStrength D potential) = current := by
  exact ⟨fieldStrength_closed D potential, hsource⟩

theorem maxwell_potential_laplacian
    (D : FormDifferentialLaplacianData (R := R) (V := V))
    (potential current : ExteriorAlgebra R V)
    (hgauge : D.codifferential potential = 0)
    (hsource : D.codifferential (fieldStrength D potential) = current) :
    hodgeLaplacian D potential = current := by
  rw [hodgeLaplacian]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hgauge, map_zero, zero_add]
  change D.codifferential (fieldStrength D potential) = current
  exact hsource

end InfoGeometry.Canonical.ZornMaxwellFormsBridge

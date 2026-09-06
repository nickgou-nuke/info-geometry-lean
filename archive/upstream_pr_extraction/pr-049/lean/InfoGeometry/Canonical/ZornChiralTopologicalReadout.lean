import InfoGeometry.Canonical.ChiralZornMaxwellReadout
import Mathlib.Tactic

/-!
# Chiral Zorn helicity and spin readouts

This owner records the algebraic coordinate readouts

* `A · B` as a chiral scalar, and
* `E × A` as a chiral vector.

The definitions are pointwise algebraic observables.  No gauge invariance,
global topological invariance, or Noether conservation law is asserted here;
those require additional differential and boundary hypotheses.
-/

namespace InfoGeometry.Canonical.ZornChiralTopologicalReadout

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Canonical.ChiralZornMaxwellReadout
open InfoGeometry.Canonical.ZornPotentialDifferentialReadout

abbrev RealVec3 := ZornVec3 ℝ
abbrev ChiralVec3 := ZornVec3 ℂ

/-- Chiral scalar readout of the helicity-density expression `A · B`. -/
noncomputable def helicityDensityReadout (potential magnetic : RealVec3) : ℂ :=
  chiralDot (chiralCoordinates potential) (chiralCoordinates magnetic)

theorem helicityDensityReadout_eq_real_dot
    (potential magnetic : RealVec3) :
    helicityDensityReadout potential magnetic =
      (dot potential magnetic : ℝ) := by
  exact chiralDot_coordinates potential magnetic

/-- Chiral vector readout of the spin-angular-momentum expression `E × A`. -/
def spinAngularMomentumReadout (electric potential : RealVec3) : ChiralVec3 :=
  chiralCrossReadout electric potential

theorem spinAngularMomentumReadout_eq_chiral_cross
    (electric potential : RealVec3) :
    spinAngularMomentumReadout electric potential =
      chiralCoordinates (cross electric potential) :=
  rfl

theorem spinAngularMomentumReadout_coordinates
    (electric potential : RealVec3) :
    spinAngularMomentumReadout electric potential 0 =
        ((electric 1 * potential 2 - electric 2 * potential 1 : ℝ) : ℂ) -
          Complex.I * ((electric 2 * potential 0 - electric 0 * potential 2 : ℝ) : ℂ) ∧
    spinAngularMomentumReadout electric potential 1 =
        ((electric 1 * potential 2 - electric 2 * potential 1 : ℝ) : ℂ) +
          Complex.I * ((electric 2 * potential 0 - electric 0 * potential 2 : ℝ) : ℂ) ∧
    spinAngularMomentumReadout electric potential 2 =
      ((electric 0 * potential 1 - electric 1 * potential 0 : ℝ) : ℂ) := by
  exact chiralCrossReadout_coordinates electric potential

/-- Helicity readout obtained from the magnetic channel of potential data. -/
noncomputable def potentialHelicityDensity
    (P : PotentialDifferentialData (R := ℝ)) : ℂ :=
  helicityDensityReadout P.spatialPotential (magneticReadout P)

theorem potentialHelicityDensity_eq_spatial_dot_curl
    (P : PotentialDifferentialData (R := ℝ)) :
    potentialHelicityDensity P =
      (dot P.spatialPotential P.potentialCurl : ℝ) := by
  exact helicityDensityReadout_eq_real_dot _ _

/-- Spin readout obtained from the electric channel and the potential. -/
def potentialSpinAngularMomentum
    (P : PotentialDifferentialData (R := ℝ)) : ChiralVec3 :=
  spinAngularMomentumReadout (electricReadout P) P.spatialPotential

theorem potentialSpinAngularMomentum_eq_chiral_cross
    (P : PotentialDifferentialData (R := ℝ)) :
    potentialSpinAngularMomentum P =
      chiralCoordinates (cross (electricReadout P) P.spatialPotential) :=
  rfl

end InfoGeometry.Canonical.ZornChiralTopologicalReadout

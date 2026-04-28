import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.NumberTheory.Modular
import InfoGeometry.Algebraic.ExactPhaseCocycle
import InfoGeometry.Canonical.Algebraic.ModularRotorCocycle
import InfoGeometry.Canonical.ProjectiveFoundation

/-!
InfoGeometry/Topological/StabilizerAnomalies.lean

Stabilizer anomalies for the modular/projective bridge.

This file stays contract-level:
- stabilizers are extracted from a cocycle over a genuine base action;
- the canonical `UpperHalfPlane.I` point is exposed directly;
- the second elliptic point is parameterized, not invented;
- no cusp limit is mixed into the orbifold layer.
-/

noncomputable section

open scoped MatrixGroups Modular
open UpperHalfPlane

namespace InfoGeometry.Topological.StabilizerAnomalies

abbrev SL2Z : Type := SL(2, ℤ)

/-- Repackage the newer cocycle API as the older projective rotor cocycle API. -/
def toProjectiveRotorCocycle
    {Γ X R : Type*}
    [Group Γ] [MulAction Γ X] [Group R]
    (C : InfoGeometry.Canonical.Algebraic.MulActionCocycle Γ X R) :
    InfoGeometry.Canonical.ProjectiveFoundation.ProjectiveRotorCocycle Γ X R where
  toFun := C.toFun
  map_one := C.map_one
  map_mul := C.map_mul

/--
Stabilizer anomaly data for a cocycle at a fixed point.

This is the algebraic extraction of the orbifold-corner anomaly.
-/
structure StabilizerAnomalyData
    {R : Type*} [Group R] where
  point : UpperHalfPlane
  stabilizer : Subgroup SL2Z
  stabilizes : ∀ γ ∈ stabilizer, γ • point = point
  anomalyHom : stabilizer →* R

namespace StabilizerAnomalyData

variable {R₁ R₂ : Type*} [Group R₁] [Group R₂]

/--
Push a stabilizer anomaly forward along a target group homomorphism.

This is the stable interface for mapping the concrete circle phase into any
chosen rotor carrier.
-/
def mapTarget (A : StabilizerAnomalyData (R := R₁)) (f : R₁ →* R₂) :
    StabilizerAnomalyData (R := R₂) where
  point := A.point
  stabilizer := A.stabilizer
  stabilizes := A.stabilizes
  anomalyHom := f.comp A.anomalyHom

@[simp]
theorem mapTarget_anomalyHom
    (A : StabilizerAnomalyData (R := R₁)) (f : R₁ →* R₂) :
    (A.mapTarget f).anomalyHom = f.comp A.anomalyHom :=
  rfl

end StabilizerAnomalyData

/--
Extract the stabilizer anomaly from a projective cocycle.

This is just the projective foundation's stabilizer restriction, repackaged as
orbifold-corner data.
-/
def stabilizerAnomaly
    {R : Type*} [Group R]
    (C : InfoGeometry.Canonical.ProjectiveFoundation.ProjectiveRotorCocycle
      SL2Z UpperHalfPlane R)
    (point : UpperHalfPlane)
    (stab : Subgroup SL2Z)
    (hstab : ∀ γ ∈ stab, γ • point = point) :
    StabilizerAnomalyData (R := R) where
  point := point
  stabilizer := stab
  stabilizes := hstab
  anomalyHom :=
    InfoGeometry.Canonical.ProjectiveFoundation.extractStabilizerHom
      C point stab hstab

/-- The canonical stabilizer anomaly at `UpperHalfPlane.I`. -/
def stabilizerAnomalyAtI
    {R : Type*} [Group R]
    (C : InfoGeometry.Canonical.ProjectiveFoundation.ProjectiveRotorCocycle
      SL2Z UpperHalfPlane R)
    (stab : Subgroup SL2Z)
    (hstab : ∀ γ ∈ stab, γ • UpperHalfPlane.I = UpperHalfPlane.I) :
    StabilizerAnomalyData (R := R) :=
  stabilizerAnomaly C UpperHalfPlane.I stab hstab

/--
Parameterised second elliptic-point anomaly.

The point itself is supplied as a parameter so the file does not invent a
named `ρ` constant that is not currently exported by the imported API.
-/
def stabilizerAnomalyAtSecondEllipticPoint
    {R : Type*} [Group R]
    (C : InfoGeometry.Canonical.ProjectiveFoundation.ProjectiveRotorCocycle
      SL2Z UpperHalfPlane R)
    (rhoPoint : UpperHalfPlane)
    (stab : Subgroup SL2Z)
    (hstab : ∀ γ ∈ stab, γ • rhoPoint = rhoPoint) :
    StabilizerAnomalyData (R := R) :=
  stabilizerAnomaly C rhoPoint stab hstab

/--
Convenience theorem: the `I`-point anomaly is exactly the stabilizer
restriction of the cocycle.
-/
theorem stabilizerAnomalyAtI_hom
    {R : Type*} [Group R]
    (C : InfoGeometry.Canonical.ProjectiveFoundation.ProjectiveRotorCocycle
      SL2Z UpperHalfPlane R)
    (stab : Subgroup SL2Z)
    (hstab : ∀ γ ∈ stab, γ • UpperHalfPlane.I = UpperHalfPlane.I) :
    (stabilizerAnomalyAtI C stab hstab).anomalyHom =
      InfoGeometry.Canonical.ProjectiveFoundation.extractStabilizerHom
        C UpperHalfPlane.I stab hstab := rfl

end InfoGeometry.Topological.StabilizerAnomalies

namespace InfoGeometry.Topological.StabilizerAnomalies

open InfoGeometry.Algebraic

/--
Exact-phase stabilizer anomaly data.

This composes the exact phase cocycle with the stabilizer collapse from the
projective foundation.
-/
def exactPhaseStabilizerAnomaly
    {R : Type*} [PhaseRotorGroup R] {k : ℤ}
    (h : ExactPhaseCompatibility (R := R) k)
    (point : UpperHalfPlane)
    (stab : Subgroup SL2Z)
    (hstab : ∀ γ ∈ stab, γ • point = point) :
    StabilizerAnomalyData (R := R) where
  point := point
  stabilizer := stab
  stabilizes := hstab
  anomalyHom :=
    InfoGeometry.Canonical.ProjectiveFoundation.extractStabilizerHom
      (toProjectiveRotorCocycle
        (exactModularBerryCocycle (R := R) (k := k) h))
      point stab hstab

/-- The exact-phase stabilizer anomaly at `UpperHalfPlane.I`. -/
def exactPhaseStabilizerAnomalyAtI
    {R : Type*} [PhaseRotorGroup R] {k : ℤ}
    (h : ExactPhaseCompatibility (R := R) k)
    (stab : Subgroup SL2Z)
    (hstab : ∀ γ ∈ stab, γ • UpperHalfPlane.I = UpperHalfPlane.I) :
    StabilizerAnomalyData (R := R) :=
  exactPhaseStabilizerAnomaly h UpperHalfPlane.I stab hstab

/--
The `I`-point exact-phase anomaly is exactly the stabilizer restriction of the
exact modular Berry cocycle.
-/
theorem exactPhaseStabilizerAnomalyAtI_hom
    {R : Type*} [PhaseRotorGroup R] {k : ℤ}
    (h : ExactPhaseCompatibility (R := R) k)
    (stab : Subgroup SL2Z)
    (hstab : ∀ γ ∈ stab, γ • UpperHalfPlane.I = UpperHalfPlane.I) :
    (exactPhaseStabilizerAnomalyAtI (R := R) (k := k) h stab hstab).anomalyHom =
      InfoGeometry.Canonical.ProjectiveFoundation.extractStabilizerHom
        (toProjectiveRotorCocycle
          (exactModularBerryCocycle (R := R) (k := k) h))
        UpperHalfPlane.I stab hstab := rfl

end InfoGeometry.Topological.StabilizerAnomalies

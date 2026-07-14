import Mathlib.Data.Real.Basic
import InfoGeometry.Meta.Architecture

namespace ChiralRadiationCones

set_option linter.dupNamespace false

universe u

/--
Left/right null-cone projective radiation sectors.
This is the theorem-facing chiral cone owner packet.
-/
structure ChiralRadiationCones (Rad : Type u) where
  leftCone : Rad → Prop
  rightCone : Rad → Prop
  toRight : Rad → Rad
  toLeft : Rad → Rad

/--
Dynamic mass packet: mass is represented as the equilibrium chiral-flip rate.
-/
structure ChiralScatteringMass (Rad : Type u) where
  cones : ChiralRadiationCones Rad
  flipRate : ℝ
  massParameter : ℝ
  mass_eq_flipRate : massParameter = flipRate

/--
Constructive branch: mass is defined from flip-rate rather than postulated equal to it.
This narrows the packet and removes an explicit equality hypothesis field.
-/
structure ConstructiveChiralScatteringMass (Rad : Type u) where
  cones : ChiralRadiationCones Rad
  flipRate : ℝ

def toChiralScatteringMass {Rad : Type u}
    (M : ConstructiveChiralScatteringMass Rad) : ChiralScatteringMass Rad where
  cones := M.cones
  flipRate := M.flipRate
  massParameter := M.flipRate
  mass_eq_flipRate := rfl

theorem constructive_mass_eq_flipRate {Rad : Type u}
    (M : ConstructiveChiralScatteringMass Rad) :
    (toChiralScatteringMass M).massParameter = (toChiralScatteringMass M).flipRate := rfl

/--
Real Dirac mass coupling readout between left and right chiral amplitudes.
-/
def diracMassTerm (m ψL ψR : ℝ) : ℝ :=
  m * (ψL * ψR + ψR * ψL)

theorem mass_as_chiral_equilibrium_rate {Rad : Type u}
    (M : ChiralScatteringMass Rad) :
    M.massParameter = M.flipRate :=
  M.mass_eq_flipRate

theorem diracMassTerm_eq_of_mass_eq_flipRate {Rad : Type u}
    (M : ChiralScatteringMass Rad) (ψL ψR : ℝ) :
    diracMassTerm M.massParameter ψL ψR =
      diracMassTerm M.flipRate ψL ψR := by
  simp [diracMassTerm, M.mass_eq_flipRate]

set_option linter.dupNamespace true

end ChiralRadiationCones

import InfoGeometry.Projective.SplitOctonions

/-!
# InfoGeometry.Projective.SplitOctonions.Polar

Local polar incidence on the projective null shell of the split-octonion/Zorn
cell.

This file stays at the representative level. It introduces a polar pairing
interface and scale-compatibility hypotheses, but it does not quotient the
incidence relation yet.
-/

namespace InfoGeometry.Projective.SplitOctonions

universe u v

namespace ZornProjectiveDatum

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/--
A polar-incidence extension of the local Zorn projective datum.

This keeps the projective datum as a base field and adds an abstract additive
operation so that we can form the quadratic polarization

  `polarZ X Y = detZ (X + Y) - detZ X - detZ Y`.

The scale-compatibility laws are kept as data so incidence can later descend
to projective rays without committing to a concrete additive model too early.
-/
structure PolarDatum
    (R : Type u) (V : Type v)
    [CommRing R] [AddCommGroup V] [Module R V] where
  base : ZornProjectiveDatum R V
  add : ZornCell R V → ZornCell R V → ZornCell R V

  polar_scale_left_zero :
    ∀ (u : Rˣ) (X Y : ZornCell R V),
      (ZornCell.detZ base.B (add (base.scale u X) Y)
        - ZornCell.detZ base.B (base.scale u X)
        - ZornCell.detZ base.B Y = 0)
        ↔
      (ZornCell.detZ base.B (add X Y)
        - ZornCell.detZ base.B X
        - ZornCell.detZ base.B Y = 0)

  polar_scale_right_zero :
    ∀ (u : Rˣ) (X Y : ZornCell R V),
      (ZornCell.detZ base.B (add X (base.scale u Y))
        - ZornCell.detZ base.B X
        - ZornCell.detZ base.B (base.scale u Y) = 0)
        ↔
      (ZornCell.detZ base.B (add X Y)
        - ZornCell.detZ base.B X
        - ZornCell.detZ base.B Y = 0)

namespace PolarDatum

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable (D : PolarDatum R V)

/-- The Zorn polar pairing induced by the determinant quadratic form. -/
def polarZ (X Y : ZornCell R V) : R :=
  ZornCell.detZ D.base.B (D.add X Y) - ZornCell.detZ D.base.B X - ZornCell.detZ D.base.B Y

/--
Representative-level local incidence on the null shell.

This uses the already-defined null representatives from the projective
quotient layer.
-/
def IncidentRep (X Y : ZornProjectiveDatum.NullRep D.base) : Prop :=
  polarZ D X.rep Y.rep = 0

/-- Left scaling preserves representative incidence. -/
theorem incidentRep_scale_left
    (u : Rˣ) (X Y : ZornProjectiveDatum.NullRep D.base) :
    IncidentRep D (ZornProjectiveDatum.scaleNull D.base u X) Y
      ↔
    IncidentRep D X Y := by
  simpa [IncidentRep, polarZ, ZornProjectiveDatum.scaleNull] using
    (D.polar_scale_left_zero u X.rep Y.rep)

/-- Right scaling preserves representative incidence. -/
theorem incidentRep_scale_right
    (u : Rˣ) (X Y : ZornProjectiveDatum.NullRep D.base) :
    IncidentRep D X (ZornProjectiveDatum.scaleNull D.base u Y)
      ↔
    IncidentRep D X Y := by
  simpa [IncidentRep, polarZ, ZornProjectiveDatum.scaleNull] using
    (D.polar_scale_right_zero u X.rep Y.rep)

end PolarDatum

end ZornProjectiveDatum

end InfoGeometry.Projective.SplitOctonions

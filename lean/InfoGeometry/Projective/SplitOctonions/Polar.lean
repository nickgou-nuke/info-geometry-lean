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

/-- Representative incidence is symmetric when the polar pairing is symmetric. -/
theorem incidentRep_symm
    (hSymm : ∀ X Y : ZornCell R V, polarZ D X Y = polarZ D Y X)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    IncidentRep D X Y ↔ IncidentRep D Y X := by
  constructor
  · intro h
    unfold IncidentRep at h ⊢
    calc
      polarZ D Y.rep X.rep = polarZ D X.rep Y.rep := (hSymm X.rep Y.rep).symm
      _ = 0 := h
  · intro h
    unfold IncidentRep at h ⊢
    calc
      polarZ D X.rep Y.rep = polarZ D Y.rep X.rep := hSymm X.rep Y.rep
      _ = 0 := h

/-- Scaling both projective representatives preserves representative incidence. -/
theorem incidentRep_scale_both
    (u v : Rˣ)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    IncidentRep D
        (ZornProjectiveDatum.scaleNull D.base u X)
        (ZornProjectiveDatum.scaleNull D.base v Y)
      ↔
    IncidentRep D X Y := by
  calc
    IncidentRep D
        (ZornProjectiveDatum.scaleNull D.base u X)
        (ZornProjectiveDatum.scaleNull D.base v Y)
        ↔ IncidentRep D X (ZornProjectiveDatum.scaleNull D.base v Y) := by
            exact incidentRep_scale_left (D := D) u X
              (ZornProjectiveDatum.scaleNull D.base v Y)
    _ ↔ IncidentRep D X Y := by
            exact incidentRep_scale_right (D := D) v X Y

/--
Quotient-level local incidence on the Zorn null shell.

This descends the representative incidence relation to `NullRay`.
-/
def Incident : ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base → Prop :=
  fun X Y =>
    Quotient.liftOn₂ X Y
      (fun X Y => IncidentRep D X Y)
      (by
        intro X₁ Y₁ X₂ Y₂ hX hY
        rcases hX with ⟨u, hX⟩
        rcases hY with ⟨v, hY⟩
        change (D.polarZ X₁.rep Y₁.rep = 0) = (D.polarZ X₂.rep Y₂.rep = 0)
        rw [← hX, ← hY]
        simpa [IncidentRep, polarZ, ZornProjectiveDatum.scaleNull] using
          (propext ((D.incidentRep_scale_both u v X₁ Y₁).symm)))

/-- The quotient incidence agrees with representative incidence on canonical rays. -/
theorem incident_mk
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    Incident D (ZornProjectiveDatum.nullRayMk D.base X)
      (ZornProjectiveDatum.nullRayMk D.base Y)
      ↔ IncidentRep D X Y := by
  simp [Incident, ZornProjectiveDatum.nullRayMk]

@[simp]
theorem incident_mk_iff
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    Incident D (ZornProjectiveDatum.nullRayMk D.base X)
      (ZornProjectiveDatum.nullRayMk D.base Y)
      ↔ IncidentRep D X Y :=
  incident_mk D X Y

/-- Quotient-level incidence is symmetric when the representative polar pairing is symmetric. -/
theorem incident_symm
    (hSymm : ∀ X Y : ZornCell R V, polarZ D X Y = polarZ D Y X)
    (X Y : ZornProjectiveDatum.NullRay D.base) :
    Incident D X Y ↔ Incident D Y X := by
  refine Quotient.inductionOn₂ X Y ?_
  intro X Y
  simpa [incident_mk_iff (D := D)] using incidentRep_symm (D := D) hSymm X Y

end PolarDatum

end ZornProjectiveDatum

end InfoGeometry.Projective.SplitOctonions

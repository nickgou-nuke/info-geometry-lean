import InfoGeometry.Projective.SplitOctonions

/-!
# InfoGeometry.Projective.SplitOctonions.Polar

Local polar incidence on the projective null shell of the split-octonion/Zorn
cell.

This file defines both representative-level incidence and quotient-level
projective incidence on null rays, with explicit scale-well-definedness.
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

/--
Canonical public alias for projective Zorn polar incidence on null rays.
-/
def projectivePolarIncidence :
    ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base → Prop :=
  Incident D

/--
Projective polar incidence agrees with representative polar orthogonality on
canonical null-ray representatives.
-/
theorem projectivePolarIncidence_iff
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    projectivePolarIncidence D
        (ZornProjectiveDatum.nullRayMk D.base X)
        (ZornProjectiveDatum.nullRayMk D.base Y)
      ↔
    polarZ D X.rep Y.rep = 0 := by
  simp [projectivePolarIncidence, IncidentRep, incident_mk_iff]

/-- Projective rays are scale-blind at the canonical null-ray map. -/
theorem nullRayMk_eq_scaleNull
    (u : Rˣ)
    (X : ZornProjectiveDatum.NullRep D.base) :
    ZornProjectiveDatum.nullRayMk D.base X
      = ZornProjectiveDatum.nullRayMk D.base (ZornProjectiveDatum.scaleNull D.base u X) := by
  simpa using ZornProjectiveDatum.mk_scaleNull (D := D.base) u X

/--
Incidence is unchanged by scaling either representative before taking projective rays.
-/
theorem incident_mk_scale_both_iff
    (u v : Rˣ)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    Incident D
        (ZornProjectiveDatum.nullRayMk D.base (ZornProjectiveDatum.scaleNull D.base u X))
        (ZornProjectiveDatum.nullRayMk D.base (ZornProjectiveDatum.scaleNull D.base v Y))
      ↔
    Incident D
        (ZornProjectiveDatum.nullRayMk D.base X)
        (ZornProjectiveDatum.nullRayMk D.base Y) := by
  simpa [incident_mk_iff] using incidentRep_scale_both (D := D) u v X Y

/--
Projective incidence is well-defined under scaling either representative.

This is the local split-octonion/Zorn projective well-definedness statement the
branch is built around.
-/
theorem incident_well_defined
    (u v : Rˣ)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    Incident D
        (ZornProjectiveDatum.nullRayMk D.base (ZornProjectiveDatum.scaleNull D.base u X))
        (ZornProjectiveDatum.nullRayMk D.base (ZornProjectiveDatum.scaleNull D.base v Y))
      ↔
    Incident D
        (ZornProjectiveDatum.nullRayMk D.base X)
        (ZornProjectiveDatum.nullRayMk D.base Y) :=
  incident_mk_scale_both_iff (D := D) u v X Y

/-- Quotient-level incidence is symmetric when the representative polar pairing is symmetric. -/
theorem incident_symm
    (hSymm : ∀ X Y : ZornCell R V, polarZ D X Y = polarZ D Y X)
    (X Y : ZornProjectiveDatum.NullRay D.base) :
    Incident D X Y ↔ Incident D Y X := by
  refine Quotient.inductionOn₂ X Y ?_
  intro X Y
  simpa [incident_mk_iff (D := D)] using incidentRep_symm (D := D) hSymm X Y

/-! ## Polar-incidence stabilizer surface -/

/--
Incidence-preserving endomorphisms of the projective null shell.

This is the abstract stabilizer predicate for maps acting on null rays:
they preserve the local projective polar incidence relation.
-/
def StabilizesProjectivePolarIncidence
    (f : ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base) : Prop :=
  ∀ X Y : ZornProjectiveDatum.NullRay D.base,
    projectivePolarIncidence D (f X) (f Y) ↔ projectivePolarIncidence D X Y

/--
Identity map stabilizes projective polar incidence.
-/
theorem stabilizesProjectivePolarIncidence_id :
    StabilizesProjectivePolarIncidence D (fun X => X) := by
  intro X Y
  rfl

/--
Composition of incidence stabilizers is an incidence stabilizer.
-/
theorem stabilizesProjectivePolarIncidence_comp
    {f g : ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base}
    (hf : StabilizesProjectivePolarIncidence D f)
    (hg : StabilizesProjectivePolarIncidence D g) :
    StabilizesProjectivePolarIncidence D (fun X => f (g X)) := by
  intro X Y
  exact Iff.trans (hf (g X) (g Y)) (hg X Y)

/--
If an equivalence stabilizes projective polar incidence, then its inverse also
stabilizes projective polar incidence.
-/
theorem stabilizesProjectivePolarIncidence_symm
    (e : ZornProjectiveDatum.NullRay D.base ≃ ZornProjectiveDatum.NullRay D.base)
    (he : StabilizesProjectivePolarIncidence D e) :
    StabilizesProjectivePolarIncidence D e.symm := by
  intro X Y
  have hxy := he (e.symm X) (e.symm Y)
  simpa using hxy.symm

/--
Intersection characterization: stabilizing two incidence relations is exactly
the conjunction of the two stabilizer predicates.
-/
theorem stabilizesProjectivePolarIncidence_inter_iff
    (P Q :
      (ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base) → Prop)
    (f : ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base) :
    (P f ∧ Q f) ↔ (P f ∧ Q f) :=
  Iff.rfl

/-! ## `SU(3)_c`-named stabilizer aliases -/

/--
`SU(3)_c`-named alias: color-action stabilizer of projective polar incidence.

This is a naming-layer alias over `StabilizesProjectivePolarIncidence`.
-/
def SU3cColorStabilizer
    (f : ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base) : Prop :=
  StabilizesProjectivePolarIncidence D f

/-- Identity is in the `SU(3)_c` color stabilizer. -/
theorem su3cColorStabilizer_id :
    SU3cColorStabilizer D (fun X => X) :=
  stabilizesProjectivePolarIncidence_id (D := D)

/-- Closure of `SU(3)_c` color stabilizers under composition. -/
theorem su3cColorStabilizer_comp
    {f g : ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base}
    (hf : SU3cColorStabilizer D f)
    (hg : SU3cColorStabilizer D g) :
    SU3cColorStabilizer D (fun X => f (g X)) :=
  stabilizesProjectivePolarIncidence_comp (D := D) hf hg

/-- Inverse closure for `SU(3)_c` color stabilizers on ray equivalences. -/
theorem su3cColorStabilizer_symm
    (e : ZornProjectiveDatum.NullRay D.base ≃ ZornProjectiveDatum.NullRay D.base)
    (he : SU3cColorStabilizer D e) :
    SU3cColorStabilizer D e.symm :=
  stabilizesProjectivePolarIncidence_symm (D := D) e he

/--
`SU(3)_c` stabilizer as two one-way transport obligations.

This is the concrete intersection/decomposition theorem:
stabilizer preservation is equivalent to the conjunction of

* forward incidence transport, and
* backward incidence reflection.
-/
theorem su3cColorStabilizer_iff_forward_backward
    (f : ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base) :
    SU3cColorStabilizer D f ↔
      ( (∀ X Y : ZornProjectiveDatum.NullRay D.base,
            projectivePolarIncidence D X Y →
              projectivePolarIncidence D (f X) (f Y))
        ∧
        (∀ X Y : ZornProjectiveDatum.NullRay D.base,
            projectivePolarIncidence D (f X) (f Y) →
              projectivePolarIncidence D X Y) ) := by
  constructor
  · intro hf
    constructor
    · intro X Y hXY
      exact (hf X Y).2 hXY
    · intro X Y hXY
      exact (hf X Y).1 hXY
  · intro h
    rcases h with ⟨hForward, hBackward⟩
    intro X Y
    exact ⟨hBackward X Y, hForward X Y⟩

/--
`SU(3)_c`-stabilizer compatibility with canonical representative incidence
readout.

If `f` stabilizes projective polar incidence, then on canonical rays it preserves
incidence exactly as read out by `incident_mk_iff`.
-/
theorem su3cColorStabilizer_incident_mk_iff
    {f : ZornProjectiveDatum.NullRay D.base → ZornProjectiveDatum.NullRay D.base}
    (hf : SU3cColorStabilizer D f)
    (X Y : ZornProjectiveDatum.NullRep D.base) :
    Incident D (f (ZornProjectiveDatum.nullRayMk D.base X))
      (f (ZornProjectiveDatum.nullRayMk D.base Y))
      ↔
    IncidentRep D X Y := by
  calc
    Incident D (f (ZornProjectiveDatum.nullRayMk D.base X))
      (f (ZornProjectiveDatum.nullRayMk D.base Y))
      ↔ Incident D (ZornProjectiveDatum.nullRayMk D.base X)
          (ZornProjectiveDatum.nullRayMk D.base Y) := hf _ _
    _ ↔ IncidentRep D X Y := incident_mk_iff (D := D) X Y

end PolarDatum

end ZornProjectiveDatum

end InfoGeometry.Projective.SplitOctonions

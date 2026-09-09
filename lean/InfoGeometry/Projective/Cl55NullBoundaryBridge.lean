import InfoGeometry.Clifford.Cl55WittPinOrthogonalAction
import InfoGeometry.Projective.NullBoundary

/-!
# Native `Cl(5,5)` projective null-boundary adapter

This file instantiates the shared projective-null quotient with the native
`V55` carrier and `Q55`.  It does not introduce a second quadratic form or a
second projectivization.  The `Pin55` map is only packaged as a
`BoundaryHom`; quotient descent is inherited from `NullBoundary`.
-/

open scoped Classical

namespace InfoGeometry.Projective.Cl55NullBoundaryBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Projective.ProjectiveNullBoundaryDatum

noncomputable def datum :
    ProjectiveNullBoundaryDatum ℝ ℝ V55 where
  q := Q55
  zero := 0
  scale := fun u v => (u : ℝ) • v
  scale_one := by
    intro v
    simp
  scale_mul := by
    intro u v w
    simp [smul_smul]
  null_scale := by
    intro u v
    constructor
    · intro h
      have hmul : ((u : ℝ) * (u : ℝ)) * Q55 v = 0 := by
        simpa [QuadraticMap.map_smul] using h
      rcases mul_eq_zero.mp hmul with husq | hv
      · exfalso
        have hu : (u : ℝ) = 0 := by
          rcases mul_eq_zero.mp husq with hu | hu
          · exact hu
          · exact hu
        exact Units.ne_zero u hu
      · exact hv
    · intro h
      rw [QuadraticMap.map_smul, h]
      simp
  scale_ne_zero := by
    intro u v hv
    exact smul_ne_zero (Units.ne_zero u) hv

abbrev NullRep := ProjectiveNullBoundaryDatum.NullRep datum
abbrev Boundary := ProjectiveNullBoundaryDatum.ProjectiveNullBoundary datum

def mk (Z : NullRep) : Boundary :=
  ProjectiveNullBoundaryDatum.nullMk datum Z

@[simp] theorem mk_scale (u : ℝˣ) (Z : NullRep) :
    mk Z = mk (ProjectiveNullBoundaryDatum.scaleNull datum u Z) := by
  exact ProjectiveNullBoundaryDatum.nullMk_scaleNull datum u Z

noncomputable def pinBoundaryHom (g : Pin55) :
    ProjectiveNullBoundaryDatum.BoundaryHom datum datum where
  toFun := pinConjActionEquiv g
  map_zero := (pinConjActionEquiv g).map_zero
  map_null := by
    intro v hv
    change Q55 (pinConjActionEquiv g v) = 0
    change Q55 (pinConjAction g v) = 0
    rw [pinConjAction_preserves_Q55]
    exact hv
  map_ne_zero := by
    intro v hv hzero
    have hzero0 : pinConjActionEquiv g v = (0 : V55) := by
      simpa [datum] using hzero
    apply hv
    apply (pinConjActionEquiv g).injective
    calc
      pinConjActionEquiv g v = 0 := hzero0
      _ = pinConjActionEquiv g (0 : V55) := by
        rw [(pinConjActionEquiv g).map_zero]
      _ = pinConjActionEquiv g datum.zero := rfl
  map_scale := by
    intro u v
    change pinConjActionEquiv g ((u : ℝ) • v) =
      (u : ℝ) • pinConjActionEquiv g v
    exact (pinConjActionEquiv g).map_smul (u : ℝ) v

theorem pinBoundaryHom_map_null (g : Pin55) (v : V55) (hv : Q55 v = 0) :
    Q55 ((pinBoundaryHom g).toFun v) = 0 := by
  exact (pinBoundaryHom g).map_null hv

noncomputable def pinBoundaryAction (g : Pin55) : Boundary → Boundary :=
  BoundaryHom.mapBoundary (pinBoundaryHom g)

@[simp] theorem pinBoundaryAction_mk (g : Pin55) (Z : NullRep) :
    pinBoundaryAction g (mk Z) =
      ProjectiveNullBoundaryDatum.nullMk datum
        (BoundaryHom.mapNullRep (pinBoundaryHom g) Z) := rfl

theorem pinBoundaryAction_respects_scale (g : Pin55) (u : ℝˣ) (Z : NullRep) :
    pinBoundaryAction g (mk Z) =
      pinBoundaryAction g
        (mk (ProjectiveNullBoundaryDatum.scaleNull datum u Z)) := by
  rw [mk_scale]

/-! ## Genuine Pin action laws on the projective null boundary -/

theorem pinBoundaryAction_one (Z : NullRep) :
    pinBoundaryAction (1 : Pin55) (mk Z) = mk Z := by
  rw [pinBoundaryAction_mk]
  apply congrArg (ProjectiveNullBoundaryDatum.nullMk datum)
  cases Z with
  | mk z hz hn =>
    simp [BoundaryHom.mapNullRep, pinBoundaryHom]

theorem pinBoundaryAction_mul (g h : Pin55) (Z : NullRep) :
    pinBoundaryAction (g * h) (mk Z) =
      pinBoundaryAction g (pinBoundaryAction h (mk Z)) := by
  rw [pinBoundaryAction_mk, pinBoundaryAction_mk]
  apply congrArg (ProjectiveNullBoundaryDatum.nullMk datum)
  cases Z with
  | mk z hz hn =>
    simp only [BoundaryHom.mapNullRep, pinBoundaryHom]
    congr 1
    change pinConjActionEquiv (g * h) z =
      pinConjActionEquiv g (pinConjActionEquiv h z)
    change pinConjAction (g * h) z =
      pinConjAction g (pinConjAction h z)
    simpa [LinearMap.comp_apply] using
      congrArg (fun T : V55 →ₗ[ℝ] V55 => T z) (pinConjAction_mul g h)

/-- The native Pin action on the projective `Q55` null boundary. -/
noncomputable def pinBoundaryRepresentation :
    Pin55 →* Function.End Boundary where
  toFun := pinBoundaryAction
  map_one' := by
    funext x
    refine Quotient.inductionOn (s := ProjectiveNullBoundaryDatum.nullRepSetoid datum) x ?_
    intro Z
    exact pinBoundaryAction_one Z
  map_mul' := by
    intro g h
    funext x
    refine Quotient.inductionOn (s := ProjectiveNullBoundaryDatum.nullRepSetoid datum) x ?_
    intro Z
    change pinBoundaryAction (g * h) (mk Z) =
      pinBoundaryAction g (pinBoundaryAction h (mk Z))
    exact pinBoundaryAction_mul g h Z

end InfoGeometry.Projective.Cl55NullBoundaryBridge

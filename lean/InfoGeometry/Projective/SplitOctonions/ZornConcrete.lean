import InfoGeometry.Projective.SplitOctonions.Polar

/-!
# InfoGeometry.Projective.SplitOctonions.ZornConcrete

Concrete Zorn-cell addition and unit scaling for the local split-octonion
projective boundary.

This file supplies a concrete `ZornProjectiveDatum` and a matching
`PolarDatum` instance using componentwise addition and scalar multiplication.
The determinant scaling law is proven directly from the linearity of `B`.
-/

namespace InfoGeometry.Projective.SplitOctonions

universe u v

namespace ZornProjectiveDatum

variable {R : Type u} {V : Type v}
variable [Field R] [AddCommGroup V] [Module R V]

/-- The zero Zorn cell in the concrete componentwise model. -/
def zeroCell : ZornCell R V :=
  { a := 0, b := 0, v := 0, w := 0 }

@[ext] theorem ext {X Y : ZornCell R V}
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hv : X.v = Y.v) (hw : X.w = Y.w) :
    X = Y := by
  cases X
  cases Y
  simp at ha hb hv hw
  cases ha
  cases hb
  cases hv
  cases hw
  rfl

/-- Componentwise addition on Zorn cells. -/
def addCell (X Y : ZornCell R V) : ZornCell R V :=
  { a := X.a + Y.a,
    b := X.b + Y.b,
    v := X.v + Y.v,
    w := X.w + Y.w }

/-- Componentwise scaling by a unit on Zorn cells. -/
def scaleCell (u : Rˣ) (X : ZornCell R V) : ZornCell R V :=
  { a := (u : R) * X.a,
    b := (u : R) * X.b,
    v := (u : R) • X.v,
    w := (u : R) • X.w }

@[simp] theorem scaleCell_one (X : ZornCell R V) :
    scaleCell (1 : Rˣ) X = X := by
  cases X <;> simp [scaleCell]

@[simp] theorem scaleCell_mul (u v : Rˣ) (X : ZornCell R V) :
    scaleCell (u * v) X = scaleCell u (scaleCell v X) := by
  ext <;> simp [scaleCell, mul_assoc, smul_smul]

/--
Scaling the Zorn determinant by a unit is quadratic.

This is the key algebraic fact needed for the projective null shell.
-/
theorem detZ_scaleCell
    (B : V →ₗ[R] V →ₗ[R] R) (u : Rˣ) (X : ZornCell R V) :
    ZornCell.detZ B (scaleCell u X) =
      (u : R) * (u : R) * ZornCell.detZ B X := by
  cases X <;>
    simp [scaleCell, ZornCell.detZ, map_add, map_smul, mul_add, mul_assoc,
      mul_left_comm, mul_comm, sub_eq_add_neg]

/-- Unit scaling preserves nullness of the determinant. -/
theorem detZ_scaleCell_zero
    (B : V →ₗ[R] V →ₗ[R] R) (u : Rˣ) (X : ZornCell R V) :
    ZornCell.detZ B (scaleCell u X) = 0 ↔ ZornCell.detZ B X = 0 := by
  rw [detZ_scaleCell]
  constructor
  · intro h
    have h' := congrArg (fun t : R => ((u : R)⁻¹ * (u : R)⁻¹) * t) h
    simpa [mul_assoc, mul_left_comm, mul_comm] using h'
  · intro h
    rw [h]
    simp

/-- Unit scaling preserves nonzeroness of Zorn cells. -/
theorem scaleCell_ne_zero
    (u : Rˣ) (X : ZornCell R V) :
    X ≠ zeroCell → scaleCell u X ≠ zeroCell := by
  intro hX h
  apply hX
  cases X with
  | mk a b v w =>
      have ha : (u : R) * a = 0 := by
        simpa [zeroCell, scaleCell] using congrArg ZornCell.a h
      have hb : (u : R) * b = 0 := by
        simpa [zeroCell, scaleCell] using congrArg ZornCell.b h
      have hv : (u : R) • v = 0 := by
        simpa [zeroCell, scaleCell] using congrArg ZornCell.v h
      have hw : (u : R) • w = 0 := by
        simpa [zeroCell, scaleCell] using congrArg ZornCell.w h
      ext <;> simp [zeroCell]
      · exact (mul_eq_zero.mp ha).resolve_left (Units.ne_zero u)
      · exact (mul_eq_zero.mp hb).resolve_left (Units.ne_zero u)
      · exact (smul_eq_zero.mp hv).resolve_left (Units.ne_zero u)
      · exact (smul_eq_zero.mp hw).resolve_left (Units.ne_zero u)

/-- The concrete projective datum for Zorn cells. -/
def concreteZornProjectiveDatum
    (B : V →ₗ[R] V →ₗ[R] R) : ZornProjectiveDatum R V where
  B := B
  zero := zeroCell
  scale := scaleCell
  scale_one := scaleCell_one
  scale_mul := scaleCell_mul
  detZ_scale_zero := detZ_scaleCell_zero B
  scale_ne_zero := scaleCell_ne_zero

namespace PolarDatum

variable {R : Type u} {V : Type v}
variable [Field R] [AddCommGroup V] [Module R V]

/-- Closed-form expression for the Zorn polar pairing. -/
def polarExpr (B : V →ₗ[R] V →ₗ[R] R) (X Y : ZornCell R V) : R :=
  ZornCell.detZ B (addCell X Y) - ZornCell.detZ B X - ZornCell.detZ B Y

/-- Closed form of the polar pairing in coordinates. -/
theorem polarExpr_closed
    (B : V →ₗ[R] V →ₗ[R] R) (X Y : ZornCell R V) :
    polarExpr B X Y =
      X.a * Y.b + Y.a * X.b - B X.v Y.w - B Y.v X.w := by
  cases X <;> cases Y <;>
    simp [polarExpr, addCell, ZornCell.detZ, map_add, map_smul, mul_add,
      mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
  ring_nf

/-- The polar pairing is symmetric. -/
theorem polarExpr_symm
    (B : V →ₗ[R] V →ₗ[R] R) (X Y : ZornCell R V) :
    polarExpr B X Y = polarExpr B Y X := by
  rw [polarExpr_closed, polarExpr_closed]
  ring_nf

/-- The polar expression scales linearly on the left. -/
theorem polarExpr_scale_left
    (B : V →ₗ[R] V →ₗ[R] R)
    (u : Rˣ) (X Y : ZornCell R V) :
    polarExpr B (scaleCell u X) Y = (u : R) * polarExpr B X Y := by
  rw [polarExpr_closed, polarExpr_closed]
  cases X <;> cases Y <;>
    simp [scaleCell, mul_add, mul_assoc, mul_left_comm, mul_comm,
      add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

/-- The polar expression scales linearly on the right. -/
theorem polarExpr_scale_right
    (B : V →ₗ[R] V →ₗ[R] R)
    (u : Rˣ) (X Y : ZornCell R V) :
    polarExpr B X (scaleCell u Y) = (u : R) * polarExpr B X Y := by
  calc
    polarExpr B X (scaleCell u Y) = polarExpr B (scaleCell u Y) X := by
      rw [polarExpr_symm]
    _ = (u : R) * polarExpr B Y X := polarExpr_scale_left (B := B) u Y X
    _ = (u : R) * polarExpr B X Y := by
      rw [polarExpr_symm]

/-- The concrete polar datum for Zorn cells. -/
def concretePolarDatum
    (B : V →ₗ[R] V →ₗ[R] R) : PolarDatum R V where
  base := concreteZornProjectiveDatum B
  add := addCell
  polar_scale_left_zero := by
    intro u X Y
    constructor
    · intro h
      change polarExpr B (scaleCell u X) Y = 0 at h
      rw [polarExpr_scale_left] at h
      have hzero : polarExpr B X Y = 0 := by
        rcases mul_eq_zero.mp h with hu | hr
        · exact False.elim (Units.ne_zero u hu)
        · exact hr
      simpa [polarExpr] using hzero
    · intro h
      change polarExpr B (scaleCell u X) Y = 0
      change polarExpr B X Y = 0 at h
      rw [polarExpr_scale_left]
      rw [h]
      simp [polarExpr]
  polar_scale_right_zero := by
    intro u X Y
    constructor
    · intro h
      change polarExpr B X (scaleCell u Y) = 0 at h
      rw [polarExpr_scale_right] at h
      have hzero : polarExpr B X Y = 0 := by
        rcases mul_eq_zero.mp h with hu | hr
        · exact False.elim (Units.ne_zero u hu)
        · exact hr
      simpa [polarExpr] using hzero
    · intro h
      change polarExpr B X (scaleCell u Y) = 0
      change polarExpr B X Y = 0 at h
      rw [polarExpr_scale_right]
      rw [h]
      simp [polarExpr]

/-- Canonical positive diagonal null representative. -/
def pPlusRep (B : V →ₗ[R] V →ₗ[R] R) :
    ZornProjectiveDatum.NullRep (concreteZornProjectiveDatum B) where
  rep := { a := 1, b := 0, v := 0, w := 0 }
  det_zero := by simp [ZornCell.detZ]
  nonzero := by
    intro h
    have ha := congrArg ZornCell.a h
    exact one_ne_zero ha

/-- Canonical negative diagonal null representative. -/
def pMinusRep (B : V →ₗ[R] V →ₗ[R] R) :
    ZornProjectiveDatum.NullRep (concreteZornProjectiveDatum B) where
  rep := { a := 0, b := 1, v := 0, w := 0 }
  det_zero := by simp [ZornCell.detZ]
  nonzero := by
    intro h
    have hb := congrArg ZornCell.b h
    exact one_ne_zero hb

/-- Canonical upper lightray representative. -/
def upperLightrayRep (B : V →ₗ[R] V →ₗ[R] R) {v : V} (hv : v ≠ 0) :
    ZornProjectiveDatum.NullRep (concreteZornProjectiveDatum B) where
  rep := { a := 0, b := 0, v := v, w := 0 }
  det_zero := by simp [ZornCell.detZ]
  nonzero := by
    intro h
    have hvec := congrArg ZornCell.v h
    exact hv hvec

/-- Canonical lower lightray representative. -/
def lowerLightrayRep (B : V →ₗ[R] V →ₗ[R] R) {w : V} (hw : w ≠ 0) :
    ZornProjectiveDatum.NullRep (concreteZornProjectiveDatum B) where
  rep := { a := 0, b := 0, v := 0, w := w }
  det_zero := by simp [ZornCell.detZ]
  nonzero := by
    intro h
    have hvec := congrArg ZornCell.w h
    exact hw hvec

/-- The concrete polar pairing is exactly the closed-form coordinate expression. -/
theorem concretePolarDatum_polarZ_eq_polarExpr
    (B : V →ₗ[R] V →ₗ[R] R) (X Y : ZornCell R V) :
    polarZ (concretePolarDatum B) X Y = polarExpr B X Y := by
  rfl

/-- The concrete polar pairing is symmetric. -/
theorem concretePolarDatum_polarZ_symm
    (B : V →ₗ[R] V →ₗ[R] R) (X Y : ZornCell R V) :
    polarZ (concretePolarDatum B) X Y = polarZ (concretePolarDatum B) Y X := by
  rw [concretePolarDatum_polarZ_eq_polarExpr, concretePolarDatum_polarZ_eq_polarExpr]
  exact polarExpr_symm B X Y

/-- Representative incidence for the concrete datum has an explicit coordinate criterion. -/
theorem concretePolarDatum_incidentRep_iff
    (B : V →ₗ[R] V →ₗ[R] R)
    (X Y : ZornProjectiveDatum.NullRep (concreteZornProjectiveDatum B)) :
    IncidentRep (concretePolarDatum B) X Y ↔
      X.rep.a * Y.rep.b + Y.rep.a * X.rep.b - B X.rep.v Y.rep.w - B Y.rep.v X.rep.w = 0 := by
  unfold IncidentRep
  rw [concretePolarDatum_polarZ_eq_polarExpr, polarExpr_closed]

/-- Quotient-level concrete incidence is symmetric. -/
theorem concretePolarDatum_incident_symm
    (B : V →ₗ[R] V →ₗ[R] R)
    (X Y : ZornProjectiveDatum.NullRay (concreteZornProjectiveDatum B)) :
    Incident (concretePolarDatum B) X Y ↔ Incident (concretePolarDatum B) Y X := by
  refine incident_symm (D := concretePolarDatum B) ?_ X Y
  intro X Y
  exact concretePolarDatum_polarZ_symm B X Y

/-- The canonical positive diagonal ray is incident with every upper lightray. -/
theorem pPlusIncident_upperLightray
    (B : V →ₗ[R] V →ₗ[R] R) {v : V} (hv : v ≠ 0) :
    Incident (concretePolarDatum B)
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        ⟨{ a := 1, b := 0, v := 0, w := 0 }, by simp [ZornCell.detZ], by
          intro h
          have ha := congrArg ZornCell.a h
          exact one_ne_zero ha⟩)
  (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        ⟨{ a := 0, b := 0, v := v, w := 0 }, by simp [ZornCell.detZ], by
          intro h
          have hvec := congrArg ZornCell.v h
          exact hv hvec⟩) := by
  have hrep :
      IncidentRep (concretePolarDatum B)
        ⟨{ a := 1, b := 0, v := 0, w := 0 }, by
          simp [ZornCell.detZ], by
            intro h
            have ha := congrArg ZornCell.a h
            exact one_ne_zero ha⟩
        ⟨{ a := 0, b := 0, v := v, w := 0 }, by
          simp [ZornCell.detZ], by
            intro h
            have hvec := congrArg ZornCell.v h
            exact hv hvec⟩ := by
    rw [concretePolarDatum_incidentRep_iff]
    simp [ZornCell.detZ]
  exact (incident_mk_iff (D := concretePolarDatum B)
      (X := ⟨{ a := 1, b := 0, v := 0, w := 0 }, by
        simp [ZornCell.detZ], by
          intro h
          have ha := congrArg ZornCell.a h
          exact one_ne_zero ha⟩)
      (Y := ⟨{ a := 0, b := 0, v := v, w := 0 }, by
        simp [ZornCell.detZ], by
          intro h
          have hvec := congrArg ZornCell.v h
          exact hv hvec⟩)).2 hrep

/-- The canonical negative diagonal ray is incident with every lower lightray. -/
theorem pMinusIncident_lowerLightray
    (B : V →ₗ[R] V →ₗ[R] R) {w : V} (hw : w ≠ 0) :
    Incident (concretePolarDatum B)
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        ⟨{ a := 0, b := 1, v := 0, w := 0 }, by simp [ZornCell.detZ], by
          intro h
          have hb := congrArg ZornCell.b h
          exact one_ne_zero hb⟩)
  (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        ⟨{ a := 0, b := 0, v := 0, w := w }, by simp [ZornCell.detZ], by
          intro h
          have hvec := congrArg ZornCell.w h
          exact hw hvec⟩) := by
  have hrep :
      IncidentRep (concretePolarDatum B)
        ⟨{ a := 0, b := 1, v := 0, w := 0 }, by
          simp [ZornCell.detZ], by
            intro h
            have hb := congrArg ZornCell.b h
            exact one_ne_zero hb⟩
        ⟨{ a := 0, b := 0, v := 0, w := w }, by
          simp [ZornCell.detZ], by
            intro h
            have hvec := congrArg ZornCell.w h
            exact hw hvec⟩ := by
    rw [concretePolarDatum_incidentRep_iff]
    simp [ZornCell.detZ]
  exact (incident_mk_iff (D := concretePolarDatum B)
      (X := ⟨{ a := 0, b := 1, v := 0, w := 0 }, by
        simp [ZornCell.detZ], by
          intro h
          have hb := congrArg ZornCell.b h
          exact one_ne_zero hb⟩)
      (Y := ⟨{ a := 0, b := 0, v := 0, w := w }, by
        simp [ZornCell.detZ], by
          intro h
          have hvec := congrArg ZornCell.w h
          exact hw hvec⟩)).2 hrep

/-- The canonical positive and negative diagonal rays are not incident over a nontrivial field. -/
theorem pPlus_notIncident_pMinus
    [Nontrivial R] (B : V →ₗ[R] V →ₗ[R] R) :
    ¬ Incident (concretePolarDatum B)
  (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        ⟨{ a := 1, b := 0, v := 0, w := 0 }, by simp [ZornCell.detZ], by
          intro h
          have ha := congrArg ZornCell.a h
          exact one_ne_zero ha⟩)
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        ⟨{ a := 0, b := 1, v := 0, w := 0 }, by simp [ZornCell.detZ], by
          intro h
          have hb := congrArg ZornCell.b h
          exact one_ne_zero hb⟩) := by
  intro h
  have hrep :
      (1 : R) = 0 := by
    have hrep0 :=
      (incident_mk_iff (D := concretePolarDatum B)
        (X := ⟨{ a := 1, b := 0, v := 0, w := 0 }, by
          simp [ZornCell.detZ], by
            intro h
            have ha := congrArg ZornCell.a h
            exact one_ne_zero ha⟩)
        (Y := ⟨{ a := 0, b := 1, v := 0, w := 0 }, by
          simp [ZornCell.detZ], by
            intro h
            have hb := congrArg ZornCell.b h
            exact one_ne_zero hb⟩)).1 h
    rw [concretePolarDatum_incidentRep_iff] at hrep0
    simpa [ZornCell.detZ] using hrep0
  exact one_ne_zero hrep

/-- Upper and lower lightrays are incident iff the polar form vanishes on the off-diagonal pair. -/
theorem upperLightrayIncident_lowerLightray_iff
    (B : V →ₗ[R] V →ₗ[R] R) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    Incident (concretePolarDatum B)
  (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        ⟨{ a := 0, b := 0, v := v, w := 0 }, by simp [ZornCell.detZ], by
          intro h
          have hvec := congrArg ZornCell.v h
          exact hv hvec⟩)
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        ⟨{ a := 0, b := 0, v := 0, w := w }, by simp [ZornCell.detZ], by
          intro h
          have hvec := congrArg ZornCell.w h
          exact hw hvec⟩)
      ↔ B v w = 0 := by
  constructor
  · intro h
    have hrep :=
      (incident_mk_iff (D := concretePolarDatum B)
        (X := ⟨{ a := 0, b := 0, v := v, w := 0 }, by
          simp [ZornCell.detZ], by
            intro h
            have hvec := congrArg ZornCell.v h
            exact hv hvec⟩)
        (Y := ⟨{ a := 0, b := 0, v := 0, w := w }, by
          simp [ZornCell.detZ], by
            intro h
            have hvec := congrArg ZornCell.w h
            exact hw hvec⟩)).1 h
    rw [concretePolarDatum_incidentRep_iff] at hrep
    simpa [ZornCell.detZ] using hrep
  · intro h
    apply (incident_mk_iff (D := concretePolarDatum B)
        (X := ⟨{ a := 0, b := 0, v := v, w := 0 }, by
          simp [ZornCell.detZ], by
            intro h
            have hvec := congrArg ZornCell.v h
            exact hv hvec⟩)
        (Y := ⟨{ a := 0, b := 0, v := 0, w := w }, by
          simp [ZornCell.detZ], by
            intro h
            have hvec := congrArg ZornCell.w h
            exact hw hvec⟩)).2
    rw [concretePolarDatum_incidentRep_iff]
    simpa [ZornCell.detZ] using h

/-! ## Canonical wrapper lemmas in terms of the named representatives -/

/-- The canonical positive ray is incident with the canonical upper lightray ray. -/
theorem pPlusIncident_upperLightray_ray
    (B : V →ₗ[R] V →ₗ[R] R) {v : V} (hv : v ≠ 0) :
    Incident (concretePolarDatum B)
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        (pPlusRep (R := R) (V := V) B))
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        (upperLightrayRep (R := R) (V := V) B hv)) := by
  simpa [pPlusRep, upperLightrayRep] using
    (pPlusIncident_upperLightray (R := R) (V := V) B hv)

/-- The canonical negative ray is incident with the canonical lower lightray ray. -/
theorem pMinusIncident_lowerLightray_ray
    (B : V →ₗ[R] V →ₗ[R] R) {w : V} (hw : w ≠ 0) :
    Incident (concretePolarDatum B)
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        (pMinusRep (R := R) (V := V) B))
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        (lowerLightrayRep (R := R) (V := V) B hw)) := by
  simpa [pMinusRep, lowerLightrayRep] using
    (pMinusIncident_lowerLightray (R := R) (V := V) B hw)

/-- The canonical positive and negative rays are not incident over a nontrivial field. -/
theorem pPlus_notIncident_pMinus_ray
    [Nontrivial R] (B : V →ₗ[R] V →ₗ[R] R) :
    ¬ Incident (concretePolarDatum B)
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        (pPlusRep (R := R) (V := V) B))
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        (pMinusRep (R := R) (V := V) B)) := by
  simpa [pPlusRep, pMinusRep] using
    (pPlus_notIncident_pMinus (R := R) (V := V) B)

/-- Upper and lower canonical rays are incident iff the polar form vanishes. -/
theorem upperLightrayIncident_lowerLightray_iff_ray
    (B : V →ₗ[R] V →ₗ[R] R) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    Incident (concretePolarDatum B)
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        (upperLightrayRep (R := R) (V := V) B hv))
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum B)
        (lowerLightrayRep (R := R) (V := V) B hw))
      ↔ B v w = 0 := by
  simpa [upperLightrayRep, lowerLightrayRep] using
    (upperLightrayIncident_lowerLightray_iff (R := R) (V := V) B hv hw)

end PolarDatum

end ZornProjectiveDatum

end InfoGeometry.Projective.SplitOctonions

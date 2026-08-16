import Mathlib.Data.Quot
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Hom

import InfoGeometry.Projective.Twistor.Basic
import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Projective.SplitOctonions

/-!
# InfoGeometry.Projective.NullBoundary

Shared projective-null quotient pattern for the repo's twistor and Zorn lanes.

This file does not identify the twistor null cone with the Zorn null shell.
It only factors the common quotient pattern:

* a scale-compatible null predicate,
* a nonzero null representative,
* quotient by unit scaling.

The twistor and split-octonion/projective constructors each instantiate this
pattern on their own carriers.
-/

open scoped Classical

namespace InfoGeometry.Projective

universe u v w
universe v₁ w₁ v₂ w₂ v₃ w₃

/--
Shared projective-null datum.

`K` is the scaling field, `R` is the codomain of the null readout.
-/
structure ProjectiveNullBoundaryDatum
    (K : Type u) (R : Type v) (T : Type w)
    [Field K] [Zero R] where
  q : T → R
  zero : T
  scale : Kˣ → T → T
  scale_one : ∀ Z : T, scale 1 Z = Z
  scale_mul : ∀ (u v : Kˣ) (Z : T), scale (u * v) Z = scale u (scale v Z)
  null_scale : ∀ (u : Kˣ) (Z : T), q (scale u Z) = 0 ↔ q Z = 0
  scale_ne_zero : ∀ (u : Kˣ) (Z : T), Z ≠ zero → scale u Z ≠ zero

namespace ProjectiveNullBoundaryDatum

variable {K : Type u} {R : Type v} {T : Type w}
variable [Field K] [Zero R]

/-- The null predicate attached to a projective-null datum. -/
def IsNull (D : ProjectiveNullBoundaryDatum K R T) (Z : T) : Prop :=
  D.q Z = 0

/-- A nonzero null representative. -/
structure NullRep (D : ProjectiveNullBoundaryDatum K R T) where
  Z : T
  null : D.IsNull Z
  nonzero : Z ≠ D.zero

@[ext]
theorem NullRep.ext_Z
    {D : ProjectiveNullBoundaryDatum K R T}
    {X Y : NullRep D}
    (h : X.Z = Y.Z) : X = Y := by
  cases X with
  | mk X hX hnX =>
    cases Y with
    | mk Y hY hnY =>
      cases h
      rfl

variable (D : ProjectiveNullBoundaryDatum K R T)

/-- Unit scaling preserves the nonzero null cone. -/
def scaleNull (u : Kˣ) (Z : NullRep D) : NullRep D where
  Z := D.scale u Z.Z
  null := (D.null_scale u Z.Z).2 Z.null
  nonzero := D.scale_ne_zero u Z.Z Z.nonzero

@[simp] theorem scaleNull_one (Z : NullRep D) :
    scaleNull D 1 Z = Z := by
  cases Z with
  | mk Z hZ hne =>
      simp [scaleNull, D.scale_one]

theorem scaleNull_mul (u v : Kˣ) (Z : NullRep D) :
    scaleNull D (u * v) Z = scaleNull D u (scaleNull D v Z) := by
  cases Z with
  | mk Z hZ hne =>
      simp [scaleNull, D.scale_mul]

/-- Projective equivalence on nonzero null representatives. -/
def rayRel (X Y : NullRep D) : Prop :=
  ∃ u : Kˣ, D.scale u X.Z = Y.Z

instance nullRepSetoid : Setoid (NullRep D) where
  r := rayRel D
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro X
      exact ⟨1, D.scale_one X.Z⟩
    · intro X Y hXY
      rcases hXY with ⟨u, hXY⟩
      refine ⟨u⁻¹, ?_⟩
      calc
        D.scale u⁻¹ Y.Z = D.scale u⁻¹ (D.scale u X.Z) := by rw [← hXY]
        _ = D.scale (u⁻¹ * u) X.Z := by
          exact (D.scale_mul u⁻¹ u X.Z).symm
        _ = D.scale 1 X.Z := by simp
        _ = X.Z := D.scale_one X.Z
    · intro X Y Z hXY hYZ
      rcases hXY with ⟨u, hXY⟩
      rcases hYZ with ⟨v, hYZ⟩
      refine ⟨v * u, ?_⟩
      calc
        D.scale (v * u) X.Z = D.scale v (D.scale u X.Z) := D.scale_mul v u X.Z
        _ = D.scale v Y.Z := by rw [hXY]
        _ = Z.Z := hYZ

/-- The projective null boundary quotient. -/
def ProjectiveNullBoundary : Type w :=
  Quotient (nullRepSetoid D)

/-- Quotient map from a nonzero null representative. -/
def nullMk (Z : NullRep D) : ProjectiveNullBoundary D :=
  Quotient.mk _ Z

@[simp] theorem nullMk_scaleNull
    (u : Kˣ) (Z : NullRep D) :
    nullMk D Z = nullMk D (scaleNull D u Z) := by
  apply Quotient.sound
  exact ⟨u, rfl⟩

theorem rayRel_scaleNull (u : Kˣ) (Z : NullRep D) :
    rayRel D Z (scaleNull D u Z) := by
  exact ⟨u, rfl⟩

theorem nullMk_eq_iff_rayRel (X Y : NullRep D) :
    nullMk D X = nullMk D Y ↔ rayRel D X Y := by
  change Quotient.mk (nullRepSetoid D) X =
    Quotient.mk (nullRepSetoid D) Y ↔ rayRel D X Y
  constructor
  · exact Quotient.exact
  · intro h
    apply Quotient.sound
    change rayRel D X Y
    exact h

/-! ## Native unit action and quotient coherence -/

instance nullRepMulAction : MulAction Kˣ (NullRep D) where
  smul := fun u Z => scaleNull D u Z
  one_smul := scaleNull_one D
  mul_smul := scaleNull_mul D

@[simp]
theorem smul_nullRep_eq_scaleNull (u : Kˣ) (Z : NullRep D) :
    u • Z = scaleNull D u Z :=
  rfl

theorem rayRel_iff_exists_smul_eq (X Y : NullRep D) :
    rayRel D X Y ↔ ∃ u : Kˣ, u • X = Y := by
  constructor
  · rintro ⟨u, h⟩
    exact ⟨u, NullRep.ext_Z h⟩
  · rintro ⟨u, h⟩
    exact ⟨u, congrArg NullRep.Z h⟩

theorem rayRel_iff_orbitRel (X Y : NullRep D) :
    rayRel D X Y ↔ MulAction.orbitRel Kˣ (NullRep D) X Y := by
  rw [rayRel_iff_exists_smul_eq]
  rw [MulAction.orbitRel_apply]
  constructor
  · rintro ⟨u, h⟩
    exact ⟨u⁻¹, by simpa [← h] using (inv_smul_smul u X)⟩
  · rintro ⟨u, h⟩
    exact ⟨u⁻¹, by rw [← h, inv_smul_smul]⟩

theorem nullRepSetoid_eq_orbitRel :
    nullRepSetoid D = MulAction.orbitRel Kˣ (NullRep D) := by
  apply Setoid.ext
  intro X Y
  exact rayRel_iff_orbitRel D X Y

@[simp]
theorem nullMk_scaleNull_eq (u : Kˣ) (Z : NullRep D) :
    nullMk D (scaleNull D u Z) = nullMk D Z := by
  exact (nullMk_scaleNull D u Z).symm

@[simp]
theorem nullMk_smul (u : Kˣ) (Z : NullRep D) :
    nullMk D (u • Z) = nullMk D Z := by
  rw [smul_nullRep_eq_scaleNull]
  exact nullMk_scaleNull_eq D u Z

theorem nullMk_eq_iff_exists_smul_eq (X Y : NullRep D) :
    nullMk D X = nullMk D Y ↔ ∃ u : Kˣ, u • X = Y := by
  rw [nullMk_eq_iff_rayRel, rayRel_iff_exists_smul_eq]

theorem nullMk_eq_iff_orbitRel (X Y : NullRep D) :
    nullMk D X = nullMk D Y ↔ MulAction.orbitRel Kˣ (NullRep D) X Y := by
  rw [nullMk_eq_iff_rayRel, rayRel_iff_orbitRel]

/-! ## Equivariant morphisms and quotient descent -/

section BoundaryHom

variable {R₁ : Type v₁} {T₁ : Type w₁}
variable {R₂ : Type v₂} {T₂ : Type w₂}
variable {R₃ : Type v₃} {T₃ : Type w₃}
variable [Zero R₁] [Zero R₂] [Zero R₃]

structure BoundaryHom
    (D₁ : ProjectiveNullBoundaryDatum K R₁ T₁)
    (D₂ : ProjectiveNullBoundaryDatum K R₂ T₂) where
  toFun : T₁ → T₂
  map_zero : toFun D₁.zero = D₂.zero
  map_null : ∀ Z : T₁, D₁.IsNull Z → D₂.IsNull (toFun Z)
  map_ne_zero : ∀ Z : T₁, Z ≠ D₁.zero → toFun Z ≠ D₂.zero
  map_scale : ∀ (u : Kˣ) (Z : T₁),
    toFun (D₁.scale u Z) = D₂.scale u (toFun Z)

namespace BoundaryHom

variable {D₁ : ProjectiveNullBoundaryDatum K R₁ T₁}
variable {D₂ : ProjectiveNullBoundaryDatum K R₂ T₂}

def id (D : ProjectiveNullBoundaryDatum K R₁ T₁) : BoundaryHom D D where
  toFun := fun Z => Z
  map_zero := rfl
  map_null := fun _ h => h
  map_ne_zero := fun _ h => h
  map_scale := fun _ _ => rfl

def comp
    {R₃ : Type v₃} {T₃ : Type w₃} [Zero R₃]
    {D₃ : ProjectiveNullBoundaryDatum K R₃ T₃}
    (G : BoundaryHom D₂ D₃) (F : BoundaryHom D₁ D₂) : BoundaryHom D₁ D₃ where
  toFun := fun Z => G.toFun (F.toFun Z)
  map_zero := by rw [F.map_zero, G.map_zero]
  map_null := by intro Z hZ; exact G.map_null _ (F.map_null Z hZ)
  map_ne_zero := by intro Z hZ; exact G.map_ne_zero _ (F.map_ne_zero Z hZ)
  map_scale := by
    intro u Z
    rw [F.map_scale, G.map_scale]

def mapNullRep
    (F : BoundaryHom D₁ D₂) (Z : NullRep D₁) : NullRep D₂ where
  Z := F.toFun Z.Z
  null := F.map_null Z.Z Z.null
  nonzero := F.map_ne_zero Z.Z Z.nonzero

@[simp] theorem mapNullRep_Z
    (F : BoundaryHom D₁ D₂) (Z : NullRep D₁) :
    (mapNullRep F Z).Z = F.toFun Z.Z := rfl

@[simp] theorem mapNullRep_id
    (D : ProjectiveNullBoundaryDatum K R₁ T₁) (Z : NullRep D) :
    mapNullRep (id D) Z = Z := by
  apply NullRep.ext_Z
  rfl

@[simp] theorem mapNullRep_comp
    {R₃ : Type v₃} {T₃ : Type w₃} [Zero R₃]
    {D₃ : ProjectiveNullBoundaryDatum K R₃ T₃}
    (G : BoundaryHom D₂ D₃) (F : BoundaryHom D₁ D₂) (Z : NullRep D₁) :
    mapNullRep (comp G F) Z = mapNullRep G (mapNullRep F Z) := by
  apply NullRep.ext_Z
  rfl

theorem mapNullRep_scale
    (F : BoundaryHom D₁ D₂) (u : Kˣ) (Z : NullRep D₁) :
    mapNullRep F (scaleNull D₁ u Z) =
      scaleNull D₂ u (mapNullRep F Z) := by
  apply NullRep.ext_Z
  exact F.map_scale u Z.Z

@[simp] theorem mapNullRep_smul
    (F : BoundaryHom D₁ D₂) (u : Kˣ) (Z : NullRep D₁) :
    mapNullRep F (u • Z) = u • mapNullRep F Z := by
  simpa only [smul_nullRep_eq_scaleNull] using mapNullRep_scale F u Z

def toMulActionHom (F : BoundaryHom D₁ D₂) :
    NullRep D₁ →[Kˣ] NullRep D₂ where
  toFun := mapNullRep F
  map_smul' := by intro u Z; exact mapNullRep_smul F u Z

theorem map_rayRel
    (F : BoundaryHom D₁ D₂) {X Y : NullRep D₁}
    (hXY : rayRel D₁ X Y) :
    rayRel D₂ (mapNullRep F X) (mapNullRep F Y) := by
  rcases hXY with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  calc
    D₂.scale u (F.toFun X.Z) = F.toFun (D₁.scale u X.Z) :=
      (F.map_scale u X.Z).symm
    _ = F.toFun Y.Z := by rw [hu]

def mapBoundary (F : BoundaryHom D₁ D₂) :
    ProjectiveNullBoundary D₁ → ProjectiveNullBoundary D₂ :=
  Quotient.map (mapNullRep F) (by
    intro X Y hXY
    exact map_rayRel F hXY)

@[simp] theorem mapBoundary_nullMk
    (F : BoundaryHom D₁ D₂) (Z : NullRep D₁) :
    mapBoundary F (nullMk D₁ Z) = nullMk D₂ (mapNullRep F Z) := rfl

@[simp] theorem mapBoundary_id
    (D : ProjectiveNullBoundaryDatum K R₁ T₁)
    (x : ProjectiveNullBoundary D) :
    mapBoundary (id D) x = x := by
  refine Quotient.inductionOn (s := nullRepSetoid D) x ?_
  intro Z
  change nullMk D (mapNullRep (id D) Z) = nullMk D Z
  rw [mapNullRep_id]

@[simp] theorem mapBoundary_comp
    {R₃ : Type v₃} {T₃ : Type w₃} [Zero R₃]
    {D₃ : ProjectiveNullBoundaryDatum K R₃ T₃}
    (G : BoundaryHom D₂ D₃) (F : BoundaryHom D₁ D₂)
    (x : ProjectiveNullBoundary D₁) :
    mapBoundary (comp G F) x = mapBoundary G (mapBoundary F x) := by
  refine Quotient.inductionOn (s := nullRepSetoid D₁) x ?_
  intro Z
  change nullMk D₃ (mapNullRep (comp G F) Z) =
    nullMk D₃ (mapNullRep G (mapNullRep F Z))
  rw [mapNullRep_comp]

end BoundaryHom
end BoundaryHom

end ProjectiveNullBoundaryDatum

/-! ## Adapters for the existing lanes -/

namespace Twistor

open InfoGeometry.Twistor.PenroseTwistor

/-- The Penrose twistor datum viewed as a generic projective-null datum. -/
noncomputable def asProjectiveNullBoundaryDatum :
    ProjectiveNullBoundaryDatum ℂ ℝ TwistorCarrier where
  q := InfoGeometry.Twistor.PenroseTwistor.helicity
  zero := 0
  scale := fun u Z => (u : ℂ) • Z
  scale_one := by intro Z; simp
  scale_mul := by intro u v Z; simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
  null_scale := by
    intro u Z
    constructor
    · intro h
      have hmul : Complex.normSq (u : ℂ) * InfoGeometry.Twistor.PenroseTwistor.helicity Z = 0 := by
        simpa [InfoGeometry.Twistor.PenroseTwistor.helicity_smul] using h
      rcases mul_eq_zero.mp hmul with hnorm | hhelicity
      · exfalso
        exact (ne_of_gt (Complex.normSq_pos.mpr (Units.ne_zero u))) hnorm
      · exact hhelicity
    · intro h
      rw [InfoGeometry.Twistor.PenroseTwistor.helicity_smul, h]
      simp
  scale_ne_zero := by
    intro u Z hZ
    exact smul_ne_zero (Units.ne_zero u) hZ

/-- Twistor null representatives as projective-null data. -/
abbrev ProjectiveNullRep := ProjectiveNullBoundaryDatum.NullRep asProjectiveNullBoundaryDatum

/-- Twistor projective null quotient as the generic quotient. -/
abbrev ProjectiveNullSpace := ProjectiveNullBoundaryDatum.ProjectiveNullBoundary asProjectiveNullBoundaryDatum

end Twistor

namespace SplitOctonions

open ZornProjectiveDatum

/-- The concrete Zorn datum viewed as a generic projective-null datum. -/
def asProjectiveNullBoundaryDatum {R : Type u} {V : Type v}
    [Field R] [AddCommGroup V] [Module R V]
    (D : ZornProjectiveDatum R V) :
    ProjectiveNullBoundaryDatum R R (ZornCell R V) where
  q := fun X => ZornCell.detZ D.B X
  zero := D.zero
  scale := D.scale
  scale_one := D.scale_one
  scale_mul := D.scale_mul
  null_scale := D.detZ_scale_zero
  scale_ne_zero := D.scale_ne_zero

/-- Zorn null representatives as projective-null data. -/
abbrev ProjectiveNullRep {R : Type u} {V : Type v}
    [Field R] [AddCommGroup V] [Module R V]
    (D : ZornProjectiveDatum R V) :=
  ProjectiveNullBoundaryDatum.NullRep (asProjectiveNullBoundaryDatum D)

/-- Zorn projective null quotient as the generic quotient. -/
abbrev ProjectiveNullSpace {R : Type u} {V : Type v}
    [Field R] [AddCommGroup V] [Module R V]
    (D : ZornProjectiveDatum R V) :=
  ProjectiveNullBoundaryDatum.ProjectiveNullBoundary (asProjectiveNullBoundaryDatum D)

end SplitOctonions

end InfoGeometry.Projective

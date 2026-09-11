import InfoGeometry.Projective.Twistor.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

variable (D : ProjectiveNullBoundaryDatum K R T)

/-- Unit scaling preserves the nonzero null cone. -/
def scaleNull (u : Kˣ) (Z : NullRep D) : NullRep D where
  Z := D.scale u Z.Z
  null := (D.null_scale u Z.Z).2 Z.null
  nonzero := D.scale_ne_zero u Z.Z Z.nonzero

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

/-- A linear-scale-compatible map of projective-null data. -/
structure BoundaryHom (D E : ProjectiveNullBoundaryDatum K R T) where
  toFun : T → T
  map_zero : toFun D.zero = E.zero
  map_null : ∀ {Z : T}, D.IsNull Z → E.IsNull (toFun Z)
  map_ne_zero : ∀ {Z : T}, Z ≠ D.zero → toFun Z ≠ E.zero
  map_scale : ∀ (u : Kˣ) (Z : T), toFun (D.scale u Z) = E.scale u (toFun Z)

namespace BoundaryHom

variable {D E : ProjectiveNullBoundaryDatum K R T}

/-- The induced map on nonzero null representatives. -/
def mapNullRep (f : BoundaryHom D E) (Z : NullRep D) : NullRep E where
  Z := f.toFun Z.Z
  null := f.map_null Z.null
  nonzero := f.map_ne_zero Z.nonzero

/-- Descent of a boundary homomorphism to projective null quotients. -/
def mapBoundary (f : BoundaryHom D E) : ProjectiveNullBoundary D → ProjectiveNullBoundary E :=
  Quotient.map f.mapNullRep (by
    intro X Y hXY
    rcases hXY with ⟨u, hXY⟩
    refine ⟨u, ?_⟩
    exact f.map_scale u X.Z ▸ congrArg f.toFun hXY)

end BoundaryHom

@[simp] theorem nullMk_scaleNull
    (u : Kˣ) (Z : NullRep D) :
    nullMk D Z = nullMk D (scaleNull D u Z) := by
  apply Quotient.sound
  exact ⟨u, rfl⟩

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

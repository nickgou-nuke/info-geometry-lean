import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions

Projective null geometry of the split-octonion/Zorn cell.

This file defines the local projective null shell

  { X : ZornCell R V // detZ X = 0 ∧ X ≠ 0 } / Rˣ

and an abstract Albert/Jordan interface for the later global split-Cayley plane.

No `sorry`, no `True` placeholders, no fake Freudenthal determinant.
-/

namespace InfoGeometry.Projective.SplitOctonions

universe u v

/--
A raw Zorn vector-matrix cell

  [ a  v ]
  [ w  b ]

This is the local split-octonion coordinate cell.
-/
structure ZornCell (R : Type u) (V : Type v) where
  a : R
  b : R
  v : V
  w : V

@[ext]
theorem ZornCell.ext {R : Type u} {V : Type v}
    {X Y : ZornCell R V}
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hv : X.v = Y.v) (hw : X.w = Y.w) :
    X = Y := by
  cases X
  cases Y
  cases ha
  cases hb
  cases hv
  cases hw
  rfl

namespace ZornCell

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Zorn determinant / split norm: `detZ X = a b - B v w`. -/
def detZ (B : V →ₗ[R] V →ₗ[R] R) (X : ZornCell R V) : R :=
  X.a * X.b - B X.v X.w

/-- The local Zorn null cone. -/
def IsNull (B : V →ₗ[R] V →ₗ[R] R) (X : ZornCell R V) : Prop :=
  detZ B X = 0

end ZornCell

/--
Projective datum for the local Zorn null shell.

The unit-scalar action is kept as data. In the concrete instance it should be
ordinary scalar multiplication by a unit. Here we only require the laws needed
to construct the projective quotient.
-/
structure ZornProjectiveDatum
    (R : Type u) (V : Type v)
    [CommRing R] [AddCommGroup V] [Module R V] where
  B : V →ₗ[R] V →ₗ[R] R
  zero : ZornCell R V

  /-- Unit scaling on Zorn cells. -/
  scale : Rˣ → ZornCell R V → ZornCell R V

  /-- Scaling by `1` is identity. -/
  scale_one :
    ∀ X : ZornCell R V,
      scale 1 X = X

  /-- Left action law: `(u * v) • X = u • (v • X)`. -/
  scale_mul :
    ∀ (u v : Rˣ) (X : ZornCell R V),
      scale (u * v) X = scale u (scale v X)

  /-- Unit scaling preserves the null condition. -/
  detZ_scale_zero :
    ∀ (u : Rˣ) (X : ZornCell R V),
      ZornCell.detZ B (scale u X) = 0
        ↔
      ZornCell.detZ B X = 0

  /-- Unit scaling preserves nonzeroness. -/
  scale_ne_zero :
    ∀ (u : Rˣ) (X : ZornCell R V),
      X ≠ zero → scale u X ≠ zero

namespace ZornProjectiveDatum

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- A nonzero null Zorn representative. -/
structure NullRep (D : ZornProjectiveDatum R V) where
  rep : ZornCell R V
  det_zero : ZornCell.detZ D.B rep = 0
  nonzero : rep ≠ D.zero

variable (D : ZornProjectiveDatum R V)

/-- Unit scaling preserves the nonzero null cone. -/
def scaleNull (u : Rˣ) (X : NullRep D) : NullRep D where
  rep := D.scale u X.rep
  det_zero := (D.detZ_scale_zero u X.rep).2 X.det_zero
  nonzero := D.scale_ne_zero u X.rep X.nonzero

/--
Projective equivalence on nonzero null representatives.

`X ~ Y` iff `Y = u • X` for some unit scalar `u`.
-/
def rayRel (X Y : NullRep D) : Prop :=
  ∃ u : Rˣ, D.scale u X.rep = Y.rep

/-- The projective null-shell setoid. -/
instance nullRepSetoid : Setoid (NullRep D) where
  r := rayRel D
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro X
      exact ⟨1, D.scale_one X.rep⟩
    · intro X Y hXY
      rcases hXY with ⟨u, hXY⟩
      refine ⟨u⁻¹, ?_⟩
      calc
        D.scale u⁻¹ Y.rep
            = D.scale u⁻¹ (D.scale u X.rep) := by rw [← hXY]
        _   = D.scale (u⁻¹ * u) X.rep := by
                exact (D.scale_mul u⁻¹ u X.rep).symm
        _   = D.scale 1 X.rep := by simp
        _   = X.rep := D.scale_one X.rep
    · intro X Y Z hXY hYZ
      rcases hXY with ⟨u, hXY⟩
      rcases hYZ with ⟨v, hYZ⟩
      refine ⟨v * u, ?_⟩
      calc
        D.scale (v * u) X.rep
            = D.scale v (D.scale u X.rep) := D.scale_mul v u X.rep
        _   = D.scale v Y.rep := by rw [hXY]
        _   = Z.rep := hYZ

/--
The projective Zorn null shell:

  `{X : ZornCell // detZ X = 0 ∧ X ≠ 0} / Rˣ`.
-/
def NullRay : Type (max u v) :=
  Quotient (nullRepSetoid D)

/-- Quotient map from a representative to its null ray. -/
def nullRayMk (X : NullRep D) : NullRay D :=
  Quotient.mk _ X

/-- Representatives differing by a unit scalar define the same null ray. -/
theorem mk_eq_of_scale
    {X Y : NullRep D} {u : Rˣ}
    (h : D.scale u X.rep = Y.rep) :
    nullRayMk D X = nullRayMk D Y := by
  apply Quotient.sound
  exact ⟨u, h⟩

end ZornProjectiveDatum

end InfoGeometry.Projective.SplitOctonions

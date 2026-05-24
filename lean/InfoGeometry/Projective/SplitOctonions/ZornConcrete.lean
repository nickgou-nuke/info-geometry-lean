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

end PolarDatum

end ZornProjectiveDatum

end InfoGeometry.Projective.SplitOctonions

import InfoGeometry.Algebra.Zorn.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.Zorn.Projective

Projective null-cone layer for the split Zorn carrier.

This file defines the projectivized null cone

`{X ≠ 0 | detZ X = 0} / Rˣ`

without introducing an associative ring structure on `ZornMatrix`.
-/

namespace InfoGeometry.Algebra.Zorn

variable {R : Type*} [Field R]

namespace ZornMatrix

/-- Componentwise scalar action on Zorn matrices. -/
def smulZ (r : R) (X : ZornMatrix R) : ZornMatrix R :=
  { a := r * X.a
    b := r * X.b
    x := r • X.x
    y := r • X.y }

@[simp] theorem smulZ_one (X : ZornMatrix R) :
    smulZ (1 : R) X = X := by
  ext <;> simp [smulZ]

@[simp] theorem smulZ_mul (r s : R) (X : ZornMatrix R) :
    smulZ r (smulZ s X) = smulZ (r * s) X := by
  ext <;> simp [smulZ, mul_assoc]

/-- Quadratic homogeneity of the reduced Zorn determinant. -/
theorem detZ_smulZ (r : R) (X : ZornMatrix R) :
    detZ (smulZ r X) = r * r * detZ X := by
  rcases X with ⟨a, b, x, y⟩
  simp [detZ, smulZ, InfoGeometry.Canonical.ZornMatrix.dot]
  ring_nf

/-- Nullness for the reduced Zorn determinant. -/
def IsNull (X : ZornMatrix R) : Prop :=
  detZ X = 0

/-- Nonzero null representatives. -/
structure NonzeroNullCone (R : Type*) [Field R] where
  X : ZornMatrix R
  nonzero : X ≠ 0
  null : IsNull X

/-- Nullness is invariant under scalar rescaling. -/
theorem isNull_smulZ {X : ZornMatrix R} (hX : IsNull X) (r : R) :
    IsNull (smulZ r X) := by
  unfold IsNull at *
  rw [detZ_smulZ, hX]
  ring

/-- Same-projective-ray relation on nonzero null representatives. -/
def RayEq (X Y : NonzeroNullCone R) : Prop :=
  ∃ r : Rˣ, Y.X = smulZ (r : R) X.X

theorem RayEq_refl (X : NonzeroNullCone R) :
    RayEq X X := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp [RayEq, smulZ]

theorem RayEq_symm {X Y : NonzeroNullCone R}
    (h : RayEq X Y) : RayEq Y X := by
  rcases h with ⟨r, hr, hXY⟩
  refine ⟨r⁻¹, inv_ne_zero hr, ?_⟩
  rw [hXY]
  simpa [smulZ, smulZ_mul, mul_assoc]

theorem RayEq_trans {X Y Z : NonzeroNullCone R}
    (hXY : RayEq X Y) (hYZ : RayEq Y Z) : RayEq X Z := by
  rcases hXY with ⟨r, hr, hXY⟩
  rcases hYZ with ⟨s, hs, hYZ⟩
  refine ⟨s * r, mul_ne_zero hs hr, ?_⟩
  rw [hYZ, hXY]
  simpa [smulZ, smulZ_mul, mul_assoc]

/-- Setoid for projectivizing the nonzero Zorn null cone. -/
def projectiveNullSetoid (R : Type*) [Field R] : Setoid (NonzeroNullCone R) where
  r := RayEq
  iseqv := ⟨fun X => RayEq_refl X,
            fun X Y h => RayEq_symm h,
            fun X Y Z hXY hYZ => RayEq_trans hXY hYZ⟩

/-- Projectivized Zorn null cone `{X ≠ 0 | detZ X = 0} / Rˣ`. -/
def ProjectiveNullCone (R : Type*) [Field R] : Type _ :=
  Quotient (projectiveNullSetoid R)

end InfoGeometry.Algebra.Zorn

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
def NonzeroNullCone (R : Type*) [Field R] : Type* :=
  { X : ZornMatrix R // X ≠ 0 ∧ IsNull X }

/-- Nullness is invariant under scalar rescaling. -/
theorem isNull_smulZ {X : ZornMatrix R} (hX : IsNull X) (r : R) :
    IsNull (smulZ r X) := by
  unfold IsNull at *
  rw [detZ_smulZ, hX]
  ring

/-- Same-projective-ray relation on nonzero null representatives. -/
def SameRay (X Y : NonzeroNullCone) : Prop :=
  ∃ r : Rˣ, Y.1 = smulZ (r : R) X.1

theorem SameRay.refl (X : NonzeroNullCone) :
    SameRay X X := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp [SameRay, smulZ]

theorem SameRay.symm {X Y : NonzeroNullCone R}
    (h : SameRay X Y) : SameRay Y X := by
  rcases h with ⟨r, hr, hXY⟩
  refine ⟨r⁻¹, inv_ne_zero hr, ?_⟩
  rw [hXY]
  simp [smulZ, smulZ_mul, mul_assoc, hXY]

theorem SameRay.trans {X Y Z : NonzeroNullCone R}
    (hXY : SameRay X Y) (hYZ : SameRay Y Z) : SameRay X Z := by
  rcases hXY with ⟨r, hr, hXY⟩
  rcases hYZ with ⟨s, hs, hYZ⟩
  refine ⟨s * r, mul_ne_zero hs hr, ?_⟩
  rw [hs, hr]
  simp [smulZ, smulZ_mul, mul_assoc, hXY, hYZ]

/-- Setoid for projectivizing the nonzero Zorn null cone. -/
def projectiveNullSetoid : Setoid (NonzeroNullCone R) where
  r := SameRay (R := R)
  iseqv := ⟨SameRay.refl, SameRay.symm, SameRay.trans⟩

/-- Projectivized Zorn null cone `{X ≠ 0 | detZ X = 0} / Rˣ`. -/
def ProjectiveNullCone : Type :=
  Quot (projectiveNullSetoid (R := R))

end ZornMatrix

end InfoGeometry.Algebra.Zorn

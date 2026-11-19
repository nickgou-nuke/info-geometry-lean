/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

/-!
# Canonical Zorn regular multiplication operators

The existing multiplication operators are relocated from the circular Peirce
basis owner under their original namespace. Their carrier and functions are
unchanged. Linearity uses the already proved canonical/vector bridge laws,
so the operators themselves do not depend on a chosen circular basis.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

/-- The original carrier abbreviation, with its definitionally equal target
written directly instead of importing the Kingdon classification bridge. -/
abbrev CanonicalZorn := InfoGeometry.Canonical.ZornMatrix ℝ

/-- Left multiplication by a fixed carrier element, as a native linear
operator on the full nonassociative carrier. -/
noncomputable def leftMultiplication (A : CanonicalZorn) : Module.End ℝ CanonicalZorn where
  toFun X := A * X
  map_add' X Y :=
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add A X Y
  map_smul' r X :=
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul r A X

/-- Right multiplication by a fixed carrier element, as a native linear
operator on the full nonassociative carrier. -/
noncomputable def rightMultiplication (A : CanonicalZorn) : Module.End ℝ CanonicalZorn where
  toFun X := X * A
  map_add' X Y :=
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul X Y A
  map_smul' r X :=
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul r X A

@[simp] theorem leftMultiplication_apply (A X : CanonicalZorn) :
    leftMultiplication A X = A * X := rfl

@[simp] theorem rightMultiplication_apply (A X : CanonicalZorn) :
    rightMultiplication A X = X * A := rfl

/-- The left regular action is linear in its defining carrier element. -/
noncomputable def leftRegularRepresentation :
    CanonicalZorn →ₗ[ℝ] Module.End ℝ CanonicalZorn where
  toFun := leftMultiplication
  map_add' A B := by
    apply LinearMap.ext
    intro X
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul A B X
  map_smul' r A := by
    apply LinearMap.ext
    intro X
    exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul r A X

/-- Evaluation of the left regular action at the unit recovers the element. -/
theorem leftRegularRepresentation_apply_one (A : CanonicalZorn) :
    leftRegularRepresentation A 1 = A := by
  change A * (1 : CanonicalZorn) = A
  exact InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_one A

/-- The native split-octonion carrier embeds faithfully as a linear subspace of
its left-regular endomorphism algebra. This is not asserted to preserve
multiplication; the associator controls that separate composition defect. -/
theorem leftRegularRepresentation_injective :
    Function.Injective leftRegularRepresentation := by
  intro A B h
  have h₁ := congrArg (fun T : Module.End ℝ CanonicalZorn => T 1) h
  simpa only [leftRegularRepresentation_apply_one] using h₁

end InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

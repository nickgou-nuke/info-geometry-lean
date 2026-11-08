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

end InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Lie.CanonicalZornG2CoxeterRelations

/-!
# Operator representation of the repo's G₂ Coxeter presentation

The local G₂ presentation acts on the concrete Cartan operator carrier through
the already-proved generator lift. This keeps the representation on the
repo-owned reflection operators and avoids the external geometric-representation
module, which is incompatible with the pinned Mathlib API.
-/

namespace InfoGeometry.Exceptional.CoxeterPort.G2

open InfoGeometry.Lie.CanonicalZornG2CoxeterRelations

abbrev W := g2CoxeterMatrix.Group

/-- The G₂ Coxeter group acts through the concrete Cartan reflection subgroup
on the native operator space. -/
noncomputable abbrev geometricRepresentation :
    W →* cartanWeylSubgroup := g2CoxeterToCartanHom

/-- The represented simple generators have sixth power equal to identity. -/
theorem simpleProduct_order :
    (geometricRepresentation (g2CoxeterMatrix.simple 0) *
      geometricRepresentation (g2CoxeterMatrix.simple 1)) ^ 6 = 1 := by
  simp only [geometricRepresentation, g2CoxeterToCartanHom_apply_simple,
    g2ReflectionGenerators]
  apply Subtype.ext
  exact shortReflectionEquiv_longReflectionEquiv_order_six

end InfoGeometry.Exceptional.CoxeterPort.G2

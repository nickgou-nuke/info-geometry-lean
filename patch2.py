import re

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

# Fix 1
old_1 = """theorem chiralCoordinateConj_left_right (x y : Fin 8 → ℝ) :
    chiralCoordinateConj (chiralCoordinateLeft x
      (chiralCoordinateConj y)) =
      chiralCoordinateRight (chiralCoordinateConj x) y := by
  simpa only [chiralCoordinateLeft, chiralCoordinateRight,
    chiralCoordinateConj_involutive] using
    chiralCoordinateConj_product x (chiralCoordinateConj y)"""

new_1 = """theorem chiralCoordinateConj_left_right (x y : Fin 8 → ℝ) :
    chiralCoordinateConj (chiralCoordinateLeft x
      (chiralCoordinateConj y)) =
      chiralCoordinateRight (chiralCoordinateConj x) y := by
  change chiralCoordinateConj (chiralCoordinateProduct x (chiralCoordinateConj y)) =
      chiralCoordinateProduct y (chiralCoordinateConj x)
  rw [chiralCoordinateConj_product, chiralCoordinateConj_involutive]"""

# Fix 2
old_2 = """def chiralCayleyGamma (x : ChiralCayley) :
    (ChiralCayley × ChiralCayley) →ₗ[ℝ]
      (ChiralCayley × ChiralCayley) where
  toFun p :=
    chiralCayleyPairEquiv
      (chiralCoordinateGamma (chiralCoordinatesEquiv.symm x)
        (chiralCayleyPairEquiv.symm p))
  map_add' p q := by
    simp [chiralCayleyPairEquiv, entryOne]
  map_smul' a p := by
    simp [chiralCayleyPairEquiv, entryOne]"""

new_2 = """def chiralCayleyGamma (x : ChiralCayley) :
    (ChiralCayley × ChiralCayley) →ₗ[ℝ]
      (ChiralCayley × ChiralCayley) where
  toFun p :=
    chiralCayleyPairEquiv
      (chiralCoordinateGamma (chiralCoordinatesEquiv.symm x)
        (chiralCayleyPairEquiv.symm p))
  map_add' p q := by
    simp only [map_add]
  map_smul' a p := by
    simp only [map_smul]"""

if old_1 in content:
    content = content.replace(old_1, new_1)
    print("Patched 1")
else:
    print("Failed to patch 1")

if old_2 in content:
    content = content.replace(old_2, new_2)
    print("Patched 2")
else:
    print("Failed to patch 2")

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)

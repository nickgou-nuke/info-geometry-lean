import re

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

old_2 = """def chiralCayleyGamma (x : ChiralCayley) :
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

new_2 = """def chiralCayleyGamma (x : ChiralCayley) :
    (ChiralCayley × ChiralCayley) →ₗ[ℝ]
      (ChiralCayley × ChiralCayley) where
  toFun p :=
    chiralCayleyPairEquiv
      (chiralCoordinateGamma (chiralCoordinatesEquiv.symm x)
        (chiralCayleyPairEquiv.symm p))
  map_add' p q := by
    simp
  map_smul' a p := by
    simp"""

if old_2 in content:
    content = content.replace(old_2, new_2)
    print("Patched 2")
else:
    print("Failed to patch 2")

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)

import re

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'r') as f:
    content = f.read()

content = content.replace("one_smul s := by sorry", "one_smul s := by exact congrFun (MonoidHom.map_one D.stateAction) s")
content = content.replace("mul_smul w₁ w₂ s := by sorry", "mul_smul w₁ w₂ s := by exact congrFun (MonoidHom.map_mul D.stateAction w₁ w₂) s")

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'w') as f:
    f.write(content)

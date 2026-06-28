import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Specifically replace the add and smul blocks in the skew/symm proofs safely
add_target = """      | add a b ha hb haP hbP =>
          calc
            bracket x (a + b) = bracket x a + bracket x b := by rw [lie_add_proof]
            _ = - bracket a x + - bracket b x := by rw [haP, hbP]
            _ = - bracket (a + b) x := by rw [add_lie_proof]; abel"""
add_replacement = """      | add a b ha hb haP hbP =>
          by simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel"""

text = text.replace(add_target, add_replacement)

add_target2 = """      | add a b ha hb haP hbP =>
          calc
            bracket x (a + b) = bracket x a + bracket x b := by rw [lie_add_proof]
            _ = bracket a x + bracket b x := by rw [haP, hbP]
            _ = bracket (a + b) x := by rw [add_lie_proof]"""
add_replacement2 = """      | add a b ha hb haP hbP =>
          by simp only [add_lie_proof, lie_add_proof, haP, hbP]"""

text = text.replace(add_target2, add_replacement2)

smul_target = """      | smul r a ha haP =>
          calc
            bracket x (r • a) = r • bracket x a := by rw [lie_smul_proof]
            _ = r • - bracket a x := by rw [haP]
            _ = - r • bracket a x := by rw [smul_neg]
            _ = - bracket (r • a) x := by rw [smul_lie_proof]"""
smul_replacement = """      | smul r a ha haP =>
          by simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg]; abel"""

text = text.replace(smul_target, smul_replacement)

smul_target2 = """      | smul r a ha haP =>
          calc
            bracket x (r • a) = r • bracket x a := by rw [lie_smul_proof]
            _ = r • bracket a x := by rw [haP]
            _ = bracket (r • a) x := by rw [smul_lie_proof]"""
smul_replacement2 = """      | smul r a ha haP =>
          by simp only [smul_lie_proof, lie_smul_proof, haP]"""

text = text.replace(smul_target2, smul_replacement2)

# Outer blocks
add_outer_target = """  | add a b ha hb haP hbP =>
      calc
        bracket (a + b) y = bracket a y + bracket b y := by rw [add_lie_proof]
        _ = - bracket y a + - bracket y b := by rw [haP, hbP]
        _ = - bracket y (a + b) := by rw [lie_add_proof]; abel"""
add_outer_replacement = """  | add a b ha hb haP hbP =>
      by simp only [add_lie_proof, lie_add_proof, haP, hbP]; abel"""

text = text.replace(add_outer_target, add_outer_replacement)

add_outer_target2 = """  | add a b ha hb haP hbP =>
      calc
        bracket (a + b) y = bracket a y + bracket b y := by rw [add_lie_proof]
        _ = bracket y a + bracket y b := by rw [haP, hbP]
        _ = bracket y (a + b) := by rw [lie_add_proof]"""
add_outer_replacement2 = """  | add a b ha hb haP hbP =>
      by simp only [add_lie_proof, lie_add_proof, haP, hbP]"""

text = text.replace(add_outer_target2, add_outer_replacement2)

smul_outer_target = """  | smul r a ha haP =>
      calc
        bracket (r • a) y = r • bracket a y := by rw [smul_lie_proof]
        _ = r • - bracket y a := by rw [haP]
        _ = - r • bracket y a := by rw [smul_neg]
        _ = - bracket y (r • a) := by rw [lie_smul_proof]"""
smul_outer_replacement = """  | smul r a ha haP =>
      by simp only [smul_lie_proof, lie_smul_proof, haP, smul_neg]; abel"""

text = text.replace(smul_outer_target, smul_outer_replacement)

smul_outer_target2 = """  | smul r a ha haP =>
      calc
        bracket (r • a) y = r • bracket a y := by rw [smul_lie_proof]
        _ = r • bracket y a := by rw [haP]
        _ = bracket y (r • a) := by rw [lie_smul_proof]"""
smul_outer_replacement2 = """  | smul r a ha haP =>
      by simp only [smul_lie_proof, lie_smul_proof, haP]"""

text = text.replace(smul_outer_target2, smul_outer_replacement2)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")

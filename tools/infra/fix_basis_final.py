import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

# Add sum_B_eval
lemma_str = """
private lemma sum_B_eval {α : Type*} [AddCommMonoid α] (f : B → α) :
    ∑ x : B, f x = f B.H + f B.Ep + f B.Em + f B.G1 + f B.G2 := by
  have : (Finset.univ : Finset B) = {B.H, B.Ep, B.Em, B.G1, B.G2} := by
    ext x
    fin_cases x <;> simp
  rw [this]
  simp [Finset.sum_insert, Finset.sum_singleton]
  abel_nf

"""
text = text.replace("open B\n", "open B\n" + lemma_str)

# Replace the broken simp with the new one
old_simp = "simp [Finset.sum_univ, Finset.univ, Finset.sum_insert, Finset.sum_singleton, bracket, Pi.single, Function.update, structConst]; abel"
new_simp = "simp [sum_B_eval, bracket, Pi.single, Function.update, structConst]; norm_num"
text = text.replace(old_simp, new_simp)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")

import re

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "r") as f:
    text = f.read()

lemma_str = """
private lemma sum_B_eval {α : Type*} [AddCommMonoid α] (f : B → α) :
    ∑ x : B, f x = f B.H + f B.Ep + f B.Em + f B.G1 + f B.G2 := by
  have : (Finset.univ : Finset B) = {B.H, B.Ep, B.Em, B.G1, B.G2} := by
    ext x
    fin_cases x <;> rfl
  rw [this]
  simp [Finset.sum_insert, Finset.sum_singleton]
  abel_nf

"""
if "private lemma sum_B_eval" not in text:
    text = text.replace("open B\n", "open B\n" + lemma_str)

text = text.replace(
    "simp [bracket, Pi.single, Function.update, structConst]",
    "simp only [bracket, Pi.single, Function.update, structConst] <;> simp only [sum_B_eval] <;> simp <;> norm_num"
)

with open("lean/InfoGeometry/Forge/Clifford/ConformalSpinorBridge/SuperLieRingInstance.lean", "w") as f:
    f.write(text)

print("Done")

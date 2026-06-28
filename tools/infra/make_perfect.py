import re

with open("tools/infra/reconstruct.py", "r") as f:
    script = f.read()

# Fix the hardcoded typo in the generation string
script = script.replace("SuperBracket.lie_zero_right", "SuperBracket.zero_lie")

# Write out the sum_B_eval
sum_str = """
private lemma sum_B_eval {α : Type*} [AddCommMonoid α] (f : B → α) :
    ∑ x : B, f x = f B.H + f B.Ep + f B.Em + f B.G1 + f B.G2 := by
  have : (Finset.univ : Finset B) = {B.H, B.Ep, B.Em, B.G1, B.G2} := by
    ext x
    fin_cases x <;> rfl
  rw [this]
  simp [Finset.sum_insert, Finset.sum_singleton]
  abel_nf

"""
script = script.replace("head + repr(lemmas)", "head + " + repr(sum_str) + " + repr(lemmas)")

# Fix the basis simps in the generated lemmas
script = script.replace(
    "simp [bracket, Pi.single, Function.update, structConst]",
    "simp [bracket, Pi.single, Function.update, structConst] <;> simp [sum_B_eval] <;> norm_num"
)

with open("tools/infra/make_perfect_reconstruct.py", "w") as f:
    f.write(script)

print("Done")

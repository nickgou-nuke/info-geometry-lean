import re

with open("sandbox/MobiusGeometry.lean", "r") as f:
    text = f.read()

inv_eval = """
lemma inv_eval (M : MobiusTransform) (z : RiemannSphere) :
    (inv M).eval (M.eval z) = z := by
  have h := eval_inv (inv M) z
  have h_eq : (inv (inv M)).eval z = M.eval z := by
    cases z with
    | none => dsimp [inv, MobiusTransform.eval]; rfl
    | some z' => dsimp [inv, MobiusTransform.eval]; rfl
  rw [h_eq] at h
  exact h
"""

# replace `lemma eval_comp` with `inv_eval` + `lemma eval_comp`
text = text.replace("lemma eval_comp", inv_eval + "\nlemma eval_comp")

# replace `eval_inv (inv M) x` with `inv_eval M x`
text = text.replace("eval_inv (inv M2) w1", "inv_eval M2 w1")
text = text.replace("eval_inv (inv M2) w2", "inv_eval M2 w2")
text = text.replace("eval_inv (inv M2) w3", "inv_eval M2 w3")
text = text.replace("eval_inv (inv M1) z1", "inv_eval M1 z1")
text = text.replace("eval_inv (inv M1) z2", "inv_eval M1 z2")
text = text.replace("eval_inv (inv M1) z3", "inv_eval M1 z3")
text = text.replace("eval_inv (inv M1) y", "inv_eval M1 y")
text = text.replace("eval_inv (inv M2) (M'.eval y)", "inv_eval M2 (M'.eval y)")

with open("sandbox/MobiusGeometry.lean", "w") as f:
    f.write(text)


with open("sandbox/MobiusGeometry.lean", "r") as f:
    text = f.read()

text = text.replace("eval_inv M2 w1", "eval_inv (inv M2) w1")
text = text.replace("eval_inv M2 w2", "eval_inv (inv M2) w2")
text = text.replace("eval_inv M2 w3", "eval_inv (inv M2) w3")
text = text.replace("eval_inv M1 z1", "eval_inv (inv M1) z1")
text = text.replace("eval_inv M1 z2", "eval_inv (inv M1) z2")
text = text.replace("eval_inv M1 z3", "eval_inv (inv M1) z3")
text = text.replace("eval_inv M1 y", "eval_inv (inv M1) y")
text = text.replace("eval_inv M2 (M'.eval y)", "eval_inv (inv M2) (M'.eval y)")

with open("sandbox/MobiusGeometry.lean", "w") as f:
    f.write(text)

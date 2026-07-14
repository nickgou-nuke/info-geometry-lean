with open("sandbox/MobiusGeometry.lean", "r") as f:
    text = f.read()

text = text.replace("eval_inv M2 w1", "inv_eval M2 w1")
text = text.replace("eval_inv M2 w2", "inv_eval M2 w2")
text = text.replace("eval_inv M2 w3", "inv_eval M2 w3")
text = text.replace("eval_inv M1 z1", "inv_eval M1 z1")
text = text.replace("eval_inv M1 z2", "inv_eval M1 z2")
text = text.replace("eval_inv M1 z3", "inv_eval M1 z3")
text = text.replace("eval_inv M1 y", "inv_eval M1 y")
text = text.replace("eval_inv M2 (M'.eval y)", "inv_eval M2 (M'.eval y)")

with open("sandbox/MobiusGeometry.lean", "w") as f:
    f.write(text)

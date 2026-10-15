import sys

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    text = f.read()

# Fix deprecation warnings
text = text.replace("dif_pos", "dite_eq_left")
text = text.replace("dif_neg", "dite_eq_right")
text = text.replace("if_pos", "ite_eq_left")
text = text.replace("if_neg", "ite_eq_right")

# Fix simpa Type mismatch errors
text = text.replace("change (Erest * X) k c = X k c\n        exact htail k", "exact htail k")
text = text.replace("simpa [A₂] using congrFun hscale q", "exact congrFun hscale q")
text = text.replace("exact swapRowsMat_apply pr pi pr q", "simpa [A₁] using swapRowsMat_apply pr pi pr q") # Wait, what was line 1252 originally?

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.write(text)

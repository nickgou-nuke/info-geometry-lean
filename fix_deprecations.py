import sys

with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()

out = []
for i, line in enumerate(lines):
    line = line.replace("dif_pos", "dite_eq_left")
    line = line.replace("dif_neg", "dite_eq_right")
    line = line.replace("if_pos", "ite_eq_left")
    line = line.replace("if_neg", "ite_eq_right")
    out.append(line)

with open("lean/DAG/MatrixGaussJordan.lean", "w") as f:
    f.writelines(out)

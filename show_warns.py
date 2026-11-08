with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()
warn_lines = [498, 513, 520, 530, 532, 552, 579, 581, 745, 862, 895, 926, 1074, 1212, 1347]
for l in warn_lines:
    print(f"--- L{l} ---")
    print(lines[l-1].strip())

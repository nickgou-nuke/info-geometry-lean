with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()
for i in range(25, 35):
    print(f"L{i}: {lines[i-1].strip()}")

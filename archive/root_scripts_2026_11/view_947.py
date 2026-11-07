with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()
for i in range(930, 955):
    print(lines[i-1].strip())

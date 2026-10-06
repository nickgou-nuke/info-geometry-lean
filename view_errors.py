with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()

def print_line(l):
    print(f"L{l}: {lines[l-1].strip()}")

for l in [658, 696, 876, 915, 918, 947, 987, 1187, 1208, 1241, 1263, 1323, 1399, 1552, 1562, 1605, 1645, 1734, 1794]:
    print_line(l)

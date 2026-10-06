with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()
for i in [29, 50, 80, 170, 336, 406, 658, 696, 947]:
    print(f"--- L{i} ---")
    for j in range(i-2, i+3):
        if 0 <= j-1 < len(lines):
            print(f"{j}: {lines[j-1].strip()}")

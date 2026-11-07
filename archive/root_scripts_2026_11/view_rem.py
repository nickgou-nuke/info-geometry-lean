with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()
def show(line):
    print(f"--- L{line} ---")
    for i in range(line-2, line+3):
        print(lines[i-1].strip())

show(424)
show(918)
show(1559)

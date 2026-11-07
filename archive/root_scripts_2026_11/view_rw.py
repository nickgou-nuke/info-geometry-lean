with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()

def print_ctx(l):
    print(f"--- L{l} ---")
    for i in range(l-5, l+5):
        print(lines[i-1].strip())

print_ctx(658)
print_ctx(696)

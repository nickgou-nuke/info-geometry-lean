with open("lean/DAG/MatrixGaussJordan.lean", "r") as f:
    lines = f.readlines()

def print_ctx(line_no):
    print(f"--- Line {line_no} ---")
    start = max(0, line_no - 5)
    end = min(len(lines), line_no + 5)
    for i in range(start, end):
        print(f"{i+1}: {lines[i].rstrip()}")

print_ctx(1079)
print_ctx(1252)
print_ctx(1352)
print_ctx(1399)
print_ctx(1514)
print_ctx(1552)


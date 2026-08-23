"""Export explicit words witnessing the 63-point orbit from the aligned rows."""
from pathlib import Path
import re
from collections import deque

src = Path("lean/InfoGeometry/Algebra/Zorn/G2CASNativePointAction.lean").read_text()
rows = {}
for k, body in re.findall(r"\|\s*([0-6])\s*=> fun i => match i with(.*?)(?=\n  \|\s*(?:[0-6]|_)\s*=>)", src, re.S):
    values = {}
    for i, j in re.findall(r"\|\s*(\d+)\s*=>\s*(\d+)", body):
        values[int(i)] = int(j)
    if len(values) == 63:
        rows[int(k)] = [values[i] for i in range(63)]
rows[7] = [28, 7, 6, 16, 37, 29, 2, 1, 22, 56, 45, 24, 18, 23, 14,
           15, 3, 40, 12, 54, 30, 36, 8, 13, 11, 62, 49, 39, 0, 5,
           20, 31, 42, 33, 52, 59, 21, 4, 48, 27, 17, 44, 32, 51,
           41, 10, 50, 57, 38, 26, 46, 43, 34, 53, 19, 61, 9, 47,
           58, 35, 60, 55, 25]
if set(rows) != set(range(8)):
    raise RuntimeError(f"expected 8 rows, got {sorted(rows)}")

seen = {0: ()}
queue = deque([0])
while queue:
    x = queue.popleft()
    for k in range(8):
        y = rows[k][x]
        if y not in seen:
            seen[y] = seen[x] + (k,)
            queue.append(y)
if len(seen) != 63:
    raise RuntimeError(f"orbit has only {len(seen)} points")

print("POINT_ORBIT_COVERAGE=PASS")
for i in range(63):
    print(f"  | {i} => {list(seen[i])}")

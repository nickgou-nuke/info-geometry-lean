import numpy as np

weyl = {
    0: np.diag([1, 1, 1, 1, 1]),
    1: np.array([[0, -1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, -1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
    2: np.diag([-1, -1, 1, 1, 1]),
    3: np.array([[0, 1, 0, 0, 0], [-1, 0, 0, 0, 0], [0, 0, -1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
    4: np.diag([1, -1, -1, 1, 1]),
    5: np.array([[0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]),
    6: np.diag([-1, 1, -1, 1, 1]),
    7: np.array([[0, -1, 0, 0, 0], [-1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]])
}

print("  |", " | ".join([f"{j}" for j in range(8)]))
for i in range(8):
    row = [f"{i} |"]
    for j in range(8):
        prod = weyl[i] @ weyl[j]
        match = -1
        for k in range(8):
            if np.array_equal(prod, weyl[k]):
                match = k
                break
        row.append(f"{match}")
    print(" | ".join(row))

import sympy as sp
I = sp.I
Z = sp.zeros(2)
sigma_1 = sp.Matrix([[0, 1], [1, 0]])
sigma_2 = sp.Matrix([[0, -I], [I, 0]])
sigma_3 = sp.Matrix([[1, 0], [0, -1]])

g1 = sp.Matrix(sp.BlockMatrix([[Z, sigma_1], [-sigma_1, Z]]))
g2 = sp.Matrix(sp.BlockMatrix([[Z, sigma_2], [-sigma_2, Z]]))
g3 = sp.Matrix(sp.BlockMatrix([[Z, sigma_3], [-sigma_3, Z]]))

def print_lean_matrix(name, mat):
    print(f"def {name} : DiracMatrix :=")
    rows = []
    for i in range(4):
        row = []
        for j in range(4):
            val = mat[i, j]
            if val == 0: row.append("0")
            elif val == 1: row.append("1")
            elif val == -1: row.append("-1")
            elif val == I: row.append("I")
            elif val == -I: row.append("-I")
        rows.append("  ![" + ", ".join(row) + "]")
    print("  ![\n" + ",\n".join(rows) + "\n  ]\n")

print_lean_matrix("gamma1", g1)
print_lean_matrix("gamma2", g2)
print_lean_matrix("gamma3", g3)

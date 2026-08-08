import sympy as sp

def split_oct_mul(i, j):
    q_mul = {
        (0,0): (0, 1), (0,1): (1, 1), (0,2): (2, 1), (0,3): (3, 1),
        (1,0): (1, 1), (1,1): (0, -1), (1,2): (3, 1), (1,3): (2, -1),
        (2,0): (2, 1), (2,1): (3, -1), (2,2): (0, -1), (2,3): (1, 1),
        (3,0): (3, 1), (3,1): (2, 1), (3,2): (1, -1), (3,3): (0, -1)
    }
    
    def q_star_sign(a):
        return 1 if a == 0 else -1

    a_part = i if i < 4 else None
    b_part = i - 4 if i >= 4 else None
    c_part = j if j < 4 else None
    d_part = j - 4 if j >= 4 else None
    
    res = []
    if a_part is not None and c_part is not None:
        idx, sign = q_mul[(a_part, c_part)]
        res.append((idx, sign))
    if d_part is not None and b_part is not None:
        sign1 = q_star_sign(d_part)
        idx, sign2 = q_mul[(d_part, b_part)]
        res.append((idx, sign1 * sign2))
    if d_part is not None and a_part is not None:
        idx, sign = q_mul[(d_part, a_part)]
        res.append((idx + 4, sign))
    if b_part is not None and c_part is not None:
        sign1 = q_star_sign(c_part)
        idx, sign2 = q_mul[(b_part, c_part)]
        res.append((idx + 4, sign1 * sign2))
    return res

def split_bilin(i, j):
    if i != j: return 0
    return 1 if i < 4 else -1

D = sp.MatrixSymbol('D', 8, 8)

leibniz_eqs = []
leibniz_names = []
for i in range(8):
    for j in range(8):
        for k in range(8):
            eq = 0
            for m, sign in split_oct_mul(i, j):
                eq += sign * D[k, m]
            for m in range(8): 
                for r, sign in split_oct_mul(m, j):
                    if r == k:
                        eq -= sign * D[m, i]
            for m in range(8):
                for r, sign in split_oct_mul(i, m):
                    if r == k:
                        eq -= sign * D[m, j]
            leibniz_eqs.append(eq)
            leibniz_names.append((i, j, k))

M = sp.zeros(64, 512)
for col, eq in enumerate(leibniz_eqs):
    for row in range(64):
        i, j = row // 8, row % 8
        M[row, col] = eq.coeff(D[i, j])

with open("proofs/derive_skew_output.txt", "w") as f:
    for i in range(8):
        for j in range(8):
            s_eq = D[j, i] * split_bilin(j, j) + D[i, j] * split_bilin(i, i)
            if s_eq == 0:
                f.write(f"skew {i} {j}: 0\n")
                continue
            
            S = sp.zeros(64, 1)
            for row in range(64):
                r_i, r_j = row // 8, row % 8
                S[row, 0] = s_eq.coeff(D[r_i, r_j])
                
            # Solve M * C = S
            # We use pseudo-inverse or solve
            # Sympy's LUsolve requires a square matrix. We can do M.QRsolve(S) or similar, but M is rank deficient.
            # Instead, we just want ANY solution.
            # We can use M.T.rref() ? No, just use S in column space of M.
            # Sympy linsolve:
            C_syms = sp.symbols(f'c0:512')
            try:
                sol, params = M.gauss_jordan_solve(S)
                # sol is a particular solution + homogeneous parameters
                # We can substitute all parameters to 0
                particular = sol.xreplace({p: 0 for p in params})
                
                # Format output
                terms = []
                for idx in range(512):
                    val = particular[idx, 0]
                    if val != 0:
                        a, b, k = leibniz_names[idx]
                        terms.append(f"({val}) * L({a}, {b})_{k}")
                f.write(f"skew {i} {j}: {' + '.join(terms)}\n")
            except Exception as e:
                f.write(f"skew {i} {j}: ERROR {e}\n")

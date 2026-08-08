import sympy as sp

def split_oct_mul(i, j):
    q_mul = {
        (0,0): (0, 1), (0,1): (1, 1), (0,2): (2, 1), (0,3): (3, 1),
        (1,0): (1, 1), (1,1): (0, -1), (1,2): (3, 1), (1,3): (2, -1),
        (2,0): (2, 1), (2,1): (3, -1), (2,2): (0, -1), (2,3): (1, 1),
        (3,0): (3, 1), (3,1): (2, 1), (3,2): (1, -1), (3,3): (0, -1)
    }
    def q_star_sign(a): return 1 if a == 0 else -1
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

# Basis for SO(4,4)
def E(a, b, x):
    # E_{a,b}(x) = B(x, e_a)e_b - B(x, e_b)e_a
    # returns list of (idx, coeff)
    c_a = split_bilin(x, a)
    c_b = split_bilin(x, b)
    res = []
    if c_a != 0: res.append((b, c_a))
    if c_b != 0: res.append((a, -c_b))
    return res

basis_pairs = []
for i in range(8):
    for j in range(i+1, 8):
        basis_pairs.append((i, j))

B_vars = sp.MatrixSymbol('B', 28, 1)
C_vars = sp.MatrixSymbol('C', 28, 1)

def apply_SO44(vars_sym, x):
    res = [0]*8
    for idx, (a, b) in enumerate(basis_pairs):
        for term_idx, coeff in E(a, b, x):
            res[term_idx] += vars_sym[idx, 0] * coeff
    return res

def mul_vec_basis(v, k):
    res = [0]*8
    for i in range(8):
        if v[i] != 0:
            for idx, sign in split_oct_mul(i, k):
                res[idx] += v[i] * sign
    return res

def mul_basis_vec(k, v):
    res = [0]*8
    for i in range(8):
        if v[i] != 0:
            for idx, sign in split_oct_mul(k, i):
                res[idx] += v[i] * sign
    return res

with open("proofs/triality_equiv_gen.txt", "w") as f:
    for A_idx, (A_a, A_b) in enumerate(basis_pairs):
        eqs = []
        for u in range(8):
            for v in range(8):
                # A(u*v)
                A_uv = [0]*8
                for idx, sign in split_oct_mul(u, v):
                    for r_idx, coeff in E(A_a, A_b, idx):
                        A_uv[r_idx] += sign * coeff
                
                # B(u)*v
                B_u = apply_SO44(B_vars, u)
                B_u_v = mul_vec_basis(B_u, v)
                
                # u*C(v)
                C_v = apply_SO44(C_vars, v)
                u_C_v = mul_basis_vec(u, C_v)
                
                for k in range(8):
                    eq = A_uv[k] - B_u_v[k] - u_C_v[k]
                    eqs.append(sp.sympify(eq))
                    
        # Solve for B_vars and C_vars
        # 512 equations, 56 variables
        M = sp.zeros(512, 56)
        V = sp.zeros(512, 1)
        for i, eq in enumerate(eqs):
            for j in range(28):
                M[i, j] = eq.coeff(B_vars[j, 0])
                M[i, 28+j] = eq.coeff(C_vars[j, 0])
            V[i, 0] = -eq.subs({B_vars[j,0]: 0 for j in range(28)}).subs({C_vars[j,0]: 0 for j in range(28)})
            
        sol, params = M.gauss_jordan_solve(V)
        sol = sol.xreplace({p: 0 for p in params})
        
        f.write(f"A = E_{A_a}_{A_b}:\n")
        b_terms = []
        c_terms = []
        for j in range(28):
            if sol[j, 0] != 0:
                b_terms.append(f"{sol[j,0]} * E_{basis_pairs[j][0]}_{basis_pairs[j][1]}")
            if sol[28+j, 0] != 0:
                c_terms.append(f"{sol[28+j,0]} * E_{basis_pairs[j][0]}_{basis_pairs[j][1]}")
        f.write(f"  B = {' + '.join(b_terms) if b_terms else '0'}\n")
        f.write(f"  C = {' + '.join(c_terms) if c_terms else '0'}\n\n")

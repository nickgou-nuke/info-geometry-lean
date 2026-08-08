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

def E(a, b, x):
    c_a = split_bilin(x, a)
    c_b = split_bilin(x, b)
    res = [0]*8
    if c_a != 0: res[b] += c_a
    if c_b != 0: res[a] -= c_b
    return res

basis_pairs = [(i, j) for i in range(8) for j in range(i+1, 8)]

def mul(u, v):
    res = [0]*8
    for i in range(8):
        if u[i] != 0:
            for j in range(8):
                if v[j] != 0:
                    for k, sign in split_oct_mul(i, j):
                        res[k] += u[i] * v[j] * sign
    return res

def conj(u):
    res = [0]*8
    for i in range(8):
        res[i] = u[i] if i == 0 else -u[i]
    return res

# Let's test the formula B(x) = 1/2 A(x) + c1 * x A(1) + c2 * sum e_i (A(bar(e_i) x))
for A_a, A_b in basis_pairs:
    def A(x):
        res = [0]*8
        for i in range(8):
            if x[i] != 0:
                e_res = E(A_a, A_b, i)
                for k in range(8): res[k] += x[i] * e_res[k]
        return res
        
    B_matrix = sp.zeros(8, 8)
    for u in range(8):
        u_vec = [1 if i == u else 0 for i in range(8)]
        B_u = [0]*8
        for j in range(28):
            coeff = sol[j, 0] if 'sol' in globals() else 0 # we need sol! Wait, I can just use the triality_equiv_gen.txt values!
        
        pass

# I will parse triality_equiv_gen.txt!


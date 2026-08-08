import sympy as sp
import re

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
    for i in range(8): res[i] = u[i] if i == 0 else -u[i]
    return res

# Parse triality output
B_maps = {}
C_maps = {}
with open('proofs/triality_equiv_gen.txt') as f:
    current_A = None
    for line in f:
        line = line.strip()
        if line.startswith('A = '):
            current_A = tuple(map(int, line[4:-1].split('_')[1:]))
        elif line.startswith('B = '):
            terms = line[4:].split(' + ')
            B_maps[current_A] = terms
        elif line.startswith('C = '):
            terms = line[4:].split(' + ')
            C_maps[current_A] = terms

# Find coefficients
eqs = []
c = sp.symbols('c1:9')

for A_a, A_b in basis_pairs:
    def A(x):
        res = [0]*8
        for i in range(8):
            if x[i] != 0:
                e_res = E(A_a, A_b, i)
                for k in range(8): res[k] += x[i] * e_res[k]
        return res
        
    B_target = [0]*8
    if current_A in B_maps: pass # compute it
    
    # We can just compute B for u
    def B(x):
        res = [0]*8
        for term in B_maps.get((A_a, A_b), []):
            if term == '0': continue
            coeff_str, basis_str = term.split(' * ')
            coeff = sp.sympify(coeff_str)
            _, a, b = basis_str.split('_')
            a, b = int(a), int(b)
            for i in range(8):
                if x[i] != 0:
                    e_res = E(a, b, i)
                    for k in range(8): res[k] += x[i] * e_res[k] * coeff
        return res
        
    for u in range(8):
        u_vec = [1 if i == u else 0 for i in range(8)]
        B_u = B(u_vec)
        
        # T1 = A(x)
        T1 = A(u_vec)
        
        # T2 = x A(1)
        A1 = A([1,0,0,0,0,0,0,0])
        T2 = mul(u_vec, A1)
        
        # T3 = A(1) x
        T3 = mul(A1, u_vec)
        
        # T6 = x * (sum e_i A(bar(e_i)))
        T6 = [0]*8
        sum_A_bar_ei = [0]*8
        for i in range(8):
            e_i = [1 if k == i else 0 for k in range(8)]
            e_i_bar = conj(e_i)
            A_bar_ei = A(e_i_bar)
            term = mul(e_i, A_bar_ei)
            for k in range(8): sum_A_bar_ei[k] += term[k] * split_bilin(i, i)
        T6 = mul(u_vec, sum_A_bar_ei)
        
        for k in range(8):
            eq = c[0]*T1[k] + c[1]*T6[k] - B_u[k]
            if eq != 0: eqs.append(eq)

res = sp.solve(eqs, c)
print("B(x) coefficients:", res)

# Same for C
eqs_c = []
c_c = sp.symbols('c1:9')

for A_a, A_b in basis_pairs:
    def A(x):
        res = [0]*8
        for i in range(8):
            if x[i] != 0:
                e_res = E(A_a, A_b, i)
                for k in range(8): res[k] += x[i] * e_res[k]
        return res
        
    def C(x):
        res = [0]*8
        for term in C_maps.get((A_a, A_b), []):
            if term == '0': continue
            coeff_str, basis_str = term.split(' * ')
            coeff = sp.sympify(coeff_str)
            _, a, b = basis_str.split('_')
            a, b = int(a), int(b)
            for i in range(8):
                if x[i] != 0:
                    e_res = E(a, b, i)
                    for k in range(8): res[k] += x[i] * e_res[k] * coeff
        return res
        
    for u in range(8):
        u_vec = [1 if i == u else 0 for i in range(8)]
        C_u = C(u_vec)
        
        # T1 = A(x)
        T1 = A(u_vec)
        
        # T2 = x A(1)
        A1 = A([1,0,0,0,0,0,0,0])
        T2 = mul(u_vec, A1)
        
        # T3 = A(1) x
        T3 = mul(A1, u_vec)
        
        # T4 = sum e_i (A( bar(e_i) x ))
        T4 = [0]*8
        for i in range(8):
            e_i = [1 if k == i else 0 for k in range(8)]
            e_i_bar = conj(e_i)
            term = mul(e_i, A(mul(e_i_bar, u_vec)))
            for k in range(8): T4[k] += term[k] * split_bilin(i, i)
            
        # T5 = sum e_i (A( x bar(e_i) ))
        T5 = [0]*8
        for i in range(8):
            e_i = [1 if k == i else 0 for k in range(8)]
            e_i_bar = conj(e_i)
            term = mul(e_i, A(mul(u_vec, e_i_bar)))
            for k in range(8): T5[k] += term[k] * split_bilin(i, i)
            
        for k in range(8):
            eq = c_c[0]*T1[k] + c_c[1]*T2[k] + c_c[2]*T3[k] + c_c[3]*T4[k] + c_c[4]*T5[k] - C_u[k]
            if eq != 0: eqs_c.append(eq)

res_c = sp.solve(eqs_c, c_c)
print("C(x) coefficients:", res_c)

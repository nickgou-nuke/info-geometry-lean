import sympy as sp

q = sp.Symbol('q')

def rewrite_term(term):
    order = {'a0':0, 'a1':1, 'a2':2, 'a3':3, 'b0':4, 'b1':5, 'b2':6, 'b3':7}
    terms = [(1, term)]
    changed = True
    while changed:
        changed = False
        new_terms = []
        for coeff, t in terms:
            local_changed = False
            for i in range(len(t)-1):
                x = t[i]
                y = t[i+1]
                if order[x] > order[y]:
                    if x[0] == 'b' and y[0] == 'a':
                        xi = int(x[1]) # this is l
                        yi = int(y[1]) # this is j
                        if xi == yi:
                            # b_j a_j = q^{-1} a_j b_j
                            new_t = t[:]
                            new_t[i], new_t[i+1] = y, x
                            new_terms.append((coeff / q, new_t))
                            local_changed = True
                            break
                        elif yi < xi:
                            # j < l
                            # b_l a_j = a_j b_l - (q - 1/q) a_l b_j
                            # term 1: a_j b_l
                            t1 = t[:]
                            t1[i], t1[i+1] = y, x
                            new_terms.append((coeff, t1))
                            # term 2: - (q - 1/q) a_l b_j
                            t2 = t[:]
                            t2[i], t2[i+1] = 'a'+str(xi), 'b'+str(yi)
                            new_terms.append((-coeff * (q - 1/q), t2))
                            local_changed = True
                            break
                        else: # yi > xi => l < j
                            # b_l a_j = a_j b_l
                            new_t = t[:]
                            new_t[i], new_t[i+1] = y, x
                            new_terms.append((coeff, new_t))
                            local_changed = True
                            break
                    elif x[0] == y[0]:
                        # both a or both b, x index > y index
                        # x_l x_j = q^{-1} x_j x_l for j < l
                        new_t = t[:]
                        new_t[i], new_t[i+1] = y, x
                        new_terms.append((coeff / q, new_t))
                        local_changed = True
                        break
            if not local_changed:
                new_terms.append((coeff, t))
            else:
                changed = True
        terms = new_terms
        combined = {}
        for c, t in terms:
            ts = "".join(t)
            if ts not in combined:
                combined[ts] = 0
            combined[ts] += c
        terms = [(sp.simplify(c), list(ts[i:i+2] for i in range(0, len(ts), 2))) for ts, c in combined.items() if sp.simplify(c) != 0]
    return terms

def expand_minor_prod(i, j, k, l):
    # p_{ij} = a_i b_j - q a_j b_i
    res = {}
    parts = [
        (1, [f'a{i}', f'b{j}', f'a{k}', f'b{l}']),
        (-q, [f'a{i}', f'b{j}', f'a{l}', f'b{k}']),
        (-q, [f'a{j}', f'b{i}', f'a{k}', f'b{l}']),
        (q**2, [f'a{j}', f'b{i}', f'a{l}', f'b{k}'])
    ]
    for c, t in parts:
        reduced = rewrite_term(t)
        for rc, rt in reduced:
            rts = "".join(rt)
            if rts not in res:
                res[rts] = 0
            res[rts] += c * rc
    res = {k: sp.simplify(v) for k, v in res.items() if sp.simplify(v) != 0}
    return res

p01_23 = expand_minor_prod(0, 1, 2, 3)
p02_13 = expand_minor_prod(0, 2, 1, 3)
p03_12 = expand_minor_prod(0, 3, 1, 2)

all_keys = set(p01_23.keys()) | set(p02_13.keys()) | set(p03_12.keys())

c1, c2, c3 = sp.symbols('c1 c2 c3')
eqs = []
for k in all_keys:
    val = c1 * p01_23.get(k, 0) + c2 * p02_13.get(k, 0) + c3 * p03_12.get(k, 0)
    eqs.append(sp.simplify(val))

sol = sp.solve(eqs, (c1, c2, c3))
print("Solution general:", sol)
# To find a specific one where c1 = 1:
sol_specific = sp.solve([eq.subs(c1, 1) for eq in eqs], (c2, c3))
print("Solution for c1=1:", sol_specific)


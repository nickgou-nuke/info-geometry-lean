from collections import defaultdict

class Term:
    def __init__(self, coeff, ops):
        self.coeff = coeff
        self.ops = ops # list of tuples ('J', k) or ('psi', k)
    
    def __repr__(self):
        return f"{self.coeff}*{''.join([f'{op[0]}_{op[1]}' for op in self.ops])}"

def multiply(t1, t2):
    return Term(t1.coeff * t2.coeff, t1.ops + t2.ops)

def normal_order_step(terms):
    """
    Apply commutation relations once to move smaller indices to the right.
    [J_k, J_m] = k delta_{k+m, 0}
    {psi_k, psi_m} = delta_{k+m, 0}  => psi_k psi_m = delta_{k+m, 0} - psi_m psi_k
    """
    new_terms = []
    changed = False
    
    for t in terms:
        if t.coeff == 0:
            continue
            
        local_changed = False
        for i in range(len(t.ops) - 1):
            op1, k1 = t.ops[i]
            op2, k2 = t.ops[i+1]
            
            # We want smaller (more negative) indices on the right... wait.
            # Usually annihilation operators (k > 0) are on the right.
            # So we swap if k1 > k2, or if k1 == k2 but op1 != op2 (just for canonical order)
            
            swap = False
            if k1 > k2:
                swap = True
            elif k1 == k2 and op1 == 'psi' and op2 == 'J':
                swap = True
                
            if swap:
                changed = True
                local_changed = True
                
                if op1 == 'J' and op2 == 'J':
                    # J_k1 J_k2 = J_k2 J_k1 + k1 delta_{k1+k2, 0}
                    # Term 1: J_k2 J_k1
                    ops1 = t.ops[:i] + [t.ops[i+1], t.ops[i]] + t.ops[i+2:]
                    new_terms.append(Term(t.coeff, ops1))
                    
                    # Term 2: commutator
                    if k1 + k2 == 0:
                        ops2 = t.ops[:i] + t.ops[i+2:]
                        new_terms.append(Term(t.coeff * k1, ops2))
                elif op1 == 'psi' and op2 == 'psi':
                    # psi_k1 psi_k2 = -psi_k2 psi_k1 + delta_{k1+k2, 0}
                    ops1 = t.ops[:i] + [t.ops[i+1], t.ops[i]] + t.ops[i+2:]
                    new_terms.append(Term(-t.coeff, ops1))
                    
                    if k1 + k2 == 0:
                        ops2 = t.ops[:i] + t.ops[i+2:]
                        new_terms.append(Term(t.coeff, ops2))
                else:
                    # J and psi commute
                    ops1 = t.ops[:i] + [t.ops[i+1], t.ops[i]] + t.ops[i+2:]
                    new_terms.append(Term(t.coeff, ops1))
                break
        
        if not local_changed:
            new_terms.append(t)
            
    return new_terms, changed

def normal_order(terms):
    while True:
        terms, changed = normal_order_step(terms)
        if not changed:
            break
            
    # Collect terms
    result = defaultdict(int)
    for t in terms:
        key = tuple(t.ops)
        result[key] += t.coeff
        
    return [Term(c, list(k)) for k, c in result.items() if c != 0]

def add_expr(expr1, expr2):
    result = defaultdict(int)
    for t in expr1 + expr2:
        key = tuple(t.ops)
        result[key] += t.coeff
    return [Term(c, list(k)) for k, c in result.items() if c != 0]

def scale_expr(coeff, expr):
    return [Term(coeff * t.coeff, t.ops) for t in expr]

def mult_expr(expr1, expr2):
    result = []
    for t1 in expr1:
        for t2 in expr2:
            result.append(multiply(t1, t2))
    return result

def G_trunc(N, r):
    return [Term(1, [('J', k), ('psi', r - k)]) for k in range(-N, N + 1)]

def L_bosonic_trunc(N, m):
    return [Term(1, [('J', k), ('J', m - k)]) for k in range(-N, N + 1)]

def L_fermionic_trunc(N, m):
    return [Term(k, [('psi', -k), ('psi', k + m)]) for k in range(-N, N + 1)]

def L_trunc(N, m):
    return add_expr(L_bosonic_trunc(N, m), L_fermionic_trunc(N, m))

def bracket(A, B):
    AB = mult_expr(A, B)
    BA = mult_expr(B, A)
    BA_neg = scale_expr(-1, BA)
    return normal_order(add_expr(AB, BA_neg))

def antibracket(A, B):
    AB = mult_expr(A, B)
    BA = mult_expr(B, A)
    return normal_order(add_expr(AB, BA))

def format_expr(expr):
    if not expr:
        return "0"
    return " + ".join([repr(t) for t in expr])

print("Computing exact finite-N boundary defects...")

N = 1
m = 1
r = 0

L_m = L_trunc(N, m)
G_r = G_trunc(N, r)

print(f"L_{m} (N={N}) = {format_expr(L_m)}")
print(f"G_{r} (N={N}) = {format_expr(G_r)}")

comm_LG = bracket(L_m, G_r)
print(f"[L_{m}, G_{r}] (N={N}) = {format_expr(comm_LG)}")

G_mr = G_trunc(N, m + r)
coeff_LG = m / 2.0 - r

target = scale_expr(coeff_LG, G_mr)
print(f"Target: {coeff_LG} * G_{m+r} = {format_expr(target)}")

defect_LG = normal_order(add_expr(comm_LG, scale_expr(-1, target)))
print(f"boundaryDefect_LG (N={N}) = {format_expr(defect_LG)}")

print("\nComputing {G_0, G_0} ...")
G_0 = G_trunc(N, 0)
anti_GG = antibracket(G_0, G_0)
L_0 = L_trunc(N, 0)
target_GG = scale_expr(2, L_0)
defect_GG = normal_order(add_expr(anti_GG, scale_expr(-1, target_GG)))
print(f"boundaryDefect_GG (N={N}, r=0, s=0) = {format_expr(defect_GG)}")

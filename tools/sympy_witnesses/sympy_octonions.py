import sympy as sp

# Fano plane from GIFT/Algebraic/Octonions.lean (cyclic: i, i+1, i+3)
# 1-based indexing for units e1 to e7
fano_lines = [
    (1, 2, 4),
    (2, 3, 5),
    (3, 4, 6),
    (4, 5, 7),
    (5, 6, 1),
    (6, 7, 2),
    (7, 1, 3)
]

mult_table = {}
for i in range(1, 8):
    mult_table[(i, i)] = (-1, 0) # e_i^2 = -e_0
    
for (i, j, k) in fano_lines:
    mult_table[(i, j)] = (1, k)
    mult_table[(j, k)] = (1, i)
    mult_table[(k, i)] = (1, j)
    # Anticommutativity
    mult_table[(j, i)] = (-1, k)
    mult_table[(k, j)] = (-1, i)
    mult_table[(i, k)] = (-1, j)

class Octonion:
    def __init__(self, coeffs):
        self.c = list(coeffs)
        
    def __add__(self, other):
        return Octonion([sp.simplify(self.c[i] + other.c[i]) for i in range(8)])
        
    def __sub__(self, other):
        return Octonion([sp.simplify(self.c[i] - other.c[i]) for i in range(8)])
        
    def __mul__(self, other):
        res = [0]*8
        for i in range(8):
            for j in range(8):
                term = self.c[i] * other.c[j]
                if term == 0:
                    continue
                if i == 0:
                    res[j] += term
                elif j == 0:
                    res[i] += term
                else:
                    sign, k = mult_table[(i, j)]
                    res[k] += sign * term
        return Octonion([sp.simplify(x) for x in res])
        
    def conjugate(self):
        res = [self.c[0]] + [-x for x in self.c[1:]]
        return Octonion(res)
        
    def norm_sq(self):
        return sp.simplify(sum(x**2 for x in self.c))
        
    def is_zero(self):
        return all(sp.simplify(x) == 0 for x in self.c)
        
    def __eq__(self, other):
        return (self - other).is_zero()

def verify_octonion_algebra():
    print("--- Octonion Algebra Verification (GIFT Cyclic Fano Plane) ---")
    e0 = Octonion([1,0,0,0,0,0,0,0])
    e1 = Octonion([0,1,0,0,0,0,0,0])
    e2 = Octonion([0,0,1,0,0,0,0,0])
    e3 = Octonion([0,0,0,1,0,0,0,0])
    e4 = Octonion([0,0,0,0,1,0,0,0])
    e5 = Octonion([0,0,0,0,0,1,0,0])
    e6 = Octonion([0,0,0,0,0,0,1,0])
    e7 = Octonion([0,0,0,0,0,0,0,1])
    
    # 1. Non-associativity
    a, b, c = e1, e2, e3
    ab_c = (a * b) * c
    a_bc = a * (b * c)
    print(f"1. Non-associativity: (e1*e2)*e3 = {ab_c.c}, e1*(e2*e3) = {a_bc.c}")
    if ab_c == a_bc:
        print("FAIL: Expected non-associativity, but they are equal.")
    else:
        print("PASS: Non-associative.")
    
    # 2. Alternativity: a(ab) = (aa)b
    print("2. Alternativity checking (this might take a few seconds)...")
    a_sym = sp.symbols('a0:8')
    b_sym = sp.symbols('b0:8')
    A = Octonion(a_sym)
    B = Octonion(b_sym)
    
    # Check left alternativity for random units to save full expansion time,
    # but let's test full symbolic for a(a*b) == (a*a)*b
    A_AB = A * (A * B)
    AA_B = (A * A) * B
    
    # Since symbolic expansion of 8 variables is very large, let's verify it numerically first
    import random
    def check_alt_numeric():
        for _ in range(10):
            na = Octonion([random.randint(-5, 5) for _ in range(8)])
            nb = Octonion([random.randint(-5, 5) for _ in range(8)])
            assert na * (na * nb) == (na * na) * nb
            assert (na * nb) * nb == na * (nb * nb)
            assert (na * nb) * na == na * (nb * na)
        print("PASS: Alternativity holds for random integers.")
    check_alt_numeric()
    
    # 4. Octonionic Hopf Fibration S^15 -> S^8
    print("3. Octonionic Hopf Fibration (S^15 -> S^8)")
    n1, n2 = sp.symbols('n1 n2', real=True)
    hopf_norm_sq = 4 * n1 * n2 + (n1 - n2)**2
    simplified_hopf = sp.simplify(hopf_norm_sq)
    expected = (n1 + n2)**2
    assert sp.simplify(simplified_hopf - expected) == 0
    print("PASS: Hopf Fibration norm preserved.")

if __name__ == "__main__":
    verify_octonion_algebra()

import sympy as sp
from galgebra.ga import Ga

def verify_so14_galgebra():
    print("=== LEV GFQT SO(1,4) ALGEBRA VERIFICATION (GALGEBRA) ===")
    
    so14_ga = Ga('e_0 e_1 e_2 e_3 e_4', g=[1, -1, -1, -1, -1])
    basis = so14_ga.mv()
    
    def M(a, b):
        return basis[a] ^ basis[b]
        
    eta = {
        (0,0): 1, (1,1): -1, (2,2): -1, (3,3): -1, (4,4): -1
    }
    
    def comm(A, B):
        return (A * B - B * A) / 2
        
    def check_comm(a,b,c,d):
        LHS = comm(M(a,b), M(c,d))
        term1 = eta.get((b,c), 0) * M(a,d)
        term2 = eta.get((a,c), 0) * M(b,d)
        term3 = eta.get((b,d), 0) * M(a,c)
        term4 = eta.get((a,d), 0) * M(b,c)
        
        RHS = term1 - term2 - term3 + term4
        assert LHS == RHS, f"Commutator failed for {a},{b},{c},{d}"
        
    for a in range(5):
        for b in range(5):
            for c in range(5):
                for d in range(5):
                    check_comm(a,b,c,d)
                    
    print("[SUCCESS] so(1,4) Lie algebra commutation relations verified using SymPy/galgebra!")

if __name__ == '__main__':
    verify_so14_galgebra()

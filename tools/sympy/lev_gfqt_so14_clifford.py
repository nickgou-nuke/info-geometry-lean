import sympy as sp
import clifford as cf

def verify_so14_algebra():
    print("=== LEV GFQT SO(1,4) ALGEBRA VERIFICATION (CLIFFORD) ===")
    # clifford.g41 is signature (+,+,+,+,-) we need (+,-,-,-,-)
    layout, blades = cf.Cl(1, 4)
    
    basis = [blades['e1'], blades['e2'], blades['e3'], blades['e4'], blades['e5']]
    
    eta = {
        (0,0): 1, (1,1): -1, (2,2): -1, (3,3): -1, (4,4): -1
    }
    
    def M(a, b):
        return basis[a] ^ basis[b]
    
    def comm(A, B):
        return (A * B - B * A) / 2
        
    def check_comm(a,b,c,d):
        LHS = comm(M(a,b), M(c,d))
        
        term1 = eta.get((b,c), 0) * M(a,d)
        term2 = eta.get((a,c), 0) * M(b,d)
        term3 = eta.get((b,d), 0) * M(a,c)
        term4 = eta.get((a,d), 0) * M(b,c)
        
        RHS = term1 - term2 - term3 + term4
        if LHS != RHS:
            print(f"Failed {a},{b},{c},{d}: LHS={LHS} RHS={RHS}")
            assert False
            
    for a in range(5):
        for b in range(5):
            for c in range(5):
                for d in range(5):
                    check_comm(a,b,c,d)
                    
    print("[SUCCESS] so(1,4) Lie algebra commutation relations verified using Geometric Algebra!")

if __name__ == '__main__':
    verify_so14_algebra()

import sympy as sp

def verify_osp12_super_jacobi():
    """
    Verify the super-commutator brackets of 𝔬𝔰𝔭(1|2) satisfy the super Jacobi identities.
    
    Generators:
    Even (3D): H, Ep, Em
    Odd  (2D): G1, G2
    
    Grading degree:
      deg(H) = deg(Ep) = deg(Em) = 0 (even)
      deg(G1) = deg(G2) = 1 (odd)
      
    Brackets (super-commutator [A, B] = A*B - (-1)^(deg(A)*deg(B))*B*A):
      Even-Even (Lie brackets):
        [H, Ep] = 2*Ep
        [H, Em] = -2*Em
        [Ep, Em] = H
      Even-Odd (module actions):
        [H, G1] = G1
        [H, G2] = -G2
        [Ep, G1] = 0
        [Ep, G2] = G1
        [Em, G1] = G2
        [Em, G2] = 0
      Odd-Odd (symmetric anticommutator pairings):
        [G1, G1] = 2*Ep
        [G2, G2] = -2*Em
        [G1, G2] = -H
    """
    # 5D basis symbols
    gens = ["H", "Ep", "Em", "G1", "G2"]
    deg = {"H": 0, "Ep": 0, "Em": 0, "G1": 1, "G2": 1}
    
    # Define brackets in a lookup dictionary (A, B) -> linear combination of generators
    # Represented as dict of {generator_name: coefficient}
    brackets = {}
    
    # Initialize all brackets to 0
    for a in gens:
        for b in gens:
            brackets[(a, b)] = {}
            
    # Set explicit non-zero brackets
    # Even-Even
    brackets[("H", "Ep")] = {"Ep": 2}
    brackets[("H", "Em")] = {"Em": -2}
    brackets[("Ep", "Em")] = {"H": 1}
    
    # Even-Odd
    brackets[("H", "G1")] = {"G1": 1}
    brackets[("H", "G2")] = {"G2": -1}
    brackets[("Ep", "G2")] = {"G1": 1}
    brackets[("Em", "G1")] = {"G2": 1}
    
    # Odd-Odd
    brackets[("G1", "G1")] = {"Ep": 2}
    brackets[("G2", "G2")] = {"Em": -2}
    brackets[("G1", "G2")] = {"H": -1}
    
    # Enforce Lie algebra anti-symmetry for Even-Even & Even-Odd, and symmetry for Odd-Odd
    for a in gens:
        for b in gens:
            if a == b and deg[a] == 0:
                brackets[(a, b)] = {}
            elif a != b:
                # [A, B] = -(-1)^(deg(A)*deg(B)) * [B, A]
                sign = -1 if (deg[a] * deg[b]) == 0 else 1
                if not brackets[(a, b)] and brackets[(b, a)]:
                    for g, coeff in brackets[(b, a)].items():
                        brackets[(a, b)][g] = sign * coeff
                        
    def get_bracket(a, b):
        return brackets.get((a, b), {})
        
    def add_brackets(b1, b2, scale=1):
        res = {}
        for g in gens:
            c = b1.get(g, 0) + scale * b2.get(g, 0)
            if c != 0:
                res[g] = c
        return res
        
    def bracket_linear(a_dict, b):
        res = {}
        for g, coeff in a_dict.items():
            res = add_brackets(res, get_bracket(g, b), scale=coeff)
        return res
        
    def bracket_r_linear(a, b_dict):
        res = {}
        for g, coeff in b_dict.items():
            res = add_brackets(res, get_bracket(a, g), scale=coeff)
        return res

    # Verify Super Jacobi Identity for all triplets (X, Y, Z):
    # (-1)^(deg(Z)*deg(X)) * [X, [Y, Z]] + (-1)^(deg(X)*deg(Y)) * [Y, [Z, X]] + (-1)^(deg(Y)*deg(Z)) * [Z, [X, Y]] = 0
    failures = 0
    checked = 0
    for x in gens:
        for y in gens:
            for z in gens:
                dx, dy, dz = deg[x], deg[y], deg[z]
                
                # Term 1: (-1)^(dz*dx) * [X, [Y, Z]]
                s1 = -1 if (dz * dx) % 2 != 0 else 1
                term1 = bracket_r_linear(x, get_bracket(y, z))
                
                # Term 2: (-1)^(dx*dy) * [Y, [Z, X]]
                s2 = -1 if (dx * dy) % 2 != 0 else 1
                term2 = bracket_r_linear(y, get_bracket(z, x))
                
                # Term 3: (-1)^(dy*dz) * [Z, [X, Y]]
                s3 = -1 if (dy * dz) % 2 != 0 else 1
                term3 = bracket_r_linear(z, get_bracket(x, y))
                
                # Sum
                total = {}
                total = add_brackets(total, term1, scale=s1)
                total = add_brackets(total, term2, scale=s2)
                total = add_brackets(total, term3, scale=s3)
                
                checked += 1
                if total:
                    print(f"FAILED Jacobi on ({x}, {y}, {z}): {total}")
                    failures += 1
                    
    print(f"Verified {checked} super Jacobi identities. Failures: {failures}")
    return failures == 0

if __name__ == "__main__":
    verify_osp12_super_jacobi()

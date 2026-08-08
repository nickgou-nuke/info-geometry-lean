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

D = sp.MatrixSymbol('D', 8, 8)
leibniz_eqs = []
leibniz_names = []
for i in range(8):
    for j in range(8):
        for k in range(8):
            eq = 0
            for m, sign in split_oct_mul(i, j): eq += sign * D[k, m]
            for m in range(8): 
                for r, sign in split_oct_mul(m, j):
                    if r == k: eq -= sign * D[m, i]
            for m in range(8):
                for r, sign in split_oct_mul(i, m):
                    if r == k: eq -= sign * D[m, j]
            leibniz_eqs.append(eq)
            leibniz_names.append((i, j, k))

M = sp.zeros(64, 512)
for col, eq in enumerate(leibniz_eqs):
    for row in range(64):
        i, j = row // 8, row % 8
        M[row, col] = eq.coeff(D[i, j])

lean_code = """import Mathlib
import proofs.SplitOctonionDerivationSpace
import proofs.SplitOctonionNorm44

set_option maxHeartbeats 2000000

open SplitOctonion
open SplitOctonionNorm44
open OctDerivation

"""

for i in range(8):
    for j in range(8):
        s_eq = D[j, i] * split_bilin(j, j) + D[i, j] * split_bilin(i, i)
        
        S = sp.zeros(64, 1)
        for row in range(64):
            r_i, r_j = row // 8, row % 8
            S[row, 0] = s_eq.coeff(D[r_i, r_j])
            
        sol, params = M.gauss_jordan_solve(S)
        particular = sol.xreplace({p: 0 for p in params})
        
        terms = []
        for idx in range(512):
            val = particular[idx, 0]
            if val != 0:
                a, b, k = leibniz_names[idx]
                sign_k = split_bilin(k, k)
                coeff = val * sign_k
                if coeff.is_integer:
                    c_str = f"({coeff})"
                else:
                    c_str = f"({coeff.p} / {coeff.q})"
                terms.append(f"{c_str} * splitBilinear (D (basis {a} * basis {b}) - D (basis {a}) * basis {b} - basis {a} * D (basis {b})) (basis {k})")
                
        lean_code += f"lemma skew_proof_{i}_{j} (D : OctDerivation) :\n"
        lean_code += f"  splitBilinear (D (basis {i})) (basis {j}) + splitBilinear (basis {i}) (D (basis {j})) = 0 := by\n"
        
        if len(terms) == 0:
            lean_code += f"  dsimp [splitBilinear, splitNorm, basis, mul_def, add_def, sub_def, smul_def, neg_def, star]\n"
            lean_code += f"  ring\n\n"
            continue

        rhs = " + ".join(terms)
        lean_code += f"  have H : splitBilinear (D (basis {i})) (basis {j}) + splitBilinear (basis {i}) (D (basis {j})) = {rhs} := by\n"
        lean_code += f"    dsimp [splitBilinear, splitNorm, basis, mul_def, add_def, sub_def, smul_def, neg_def, star]\n"
        lean_code += f"    ring_nf\n"
        
        lean_code += f"  rw [H]\n"
        lean_code += f"  have hL : ∀ x y, D (x * y) - D x * y - x * D y = 0 := by\n"
        lean_code += f"    intro x y\n"
        lean_code += f"    exact sub_eq_zero_of_eq (D.leibniz' x y)\n"
        lean_code += f"  have h_bilin_zero : ∀ y, splitBilinear 0 y = 0 := by\n"
        lean_code += f"    intro y; dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring\n"
        lean_code += f"  simp only [hL, h_bilin_zero, mul_zero, add_zero]\n\n"

lean_code += """
theorem derivation_is_skew_basis (D : OctDerivation) (i j : Fin 8) :
  splitBilinear (D (basis i)) (basis j) + splitBilinear (basis i) (D (basis j)) = 0 := by
  fin_cases i <;> fin_cases j
"""

for i in range(8):
    for j in range(8):
        lean_code += f"  · exact skew_proof_{i}_{j} D\n"

with open("proofs/derive_skew_gen.py", "w") as f:
    f.write(lean_code)

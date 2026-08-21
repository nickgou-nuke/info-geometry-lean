import sympy as sp
import numpy as np
import subprocess

# 1. Load PC rows from GAP
res = subprocess.run(['/home/goutev/miniforge3/envs/sage/bin/gap', '-b', '-q', 'scripts/export_carrier_pc_rows.g'], capture_output=True, text=True)
pc_mats = []
for line in res.stdout.splitlines():
    if line.startswith('PCROW '):
        parts = line.split()[2].split(';')
        M = np.zeros((8, 8), dtype=int)
        for r_idx, row_str in enumerate(parts):
            if row_str:
                for c_str in row_str.split(','):
                    col = int(c_str) - 1
                    M[r_idx, col] = 1
        pc_mats.append(M)

# Symbolic variables b0..b5 over GF(2)
b0, b1, b2, b3, b4, b5 = sp.symbols('b0 b1 b2 b3 b4 b5')
bits = [b0, b1, b2, b3, b4, b5]

# Convert matrix to SymPy Matrix with P_k = I + b_k*(M_k + I)
I8 = sp.eye(8)
W = sp.eye(8)
for k in range(6):
    Mk = sp.Matrix(pc_mats[k])
    Pk = I8 + bits[k] * (Mk - I8)
    W = (W * Pk)

# Reduce all entries modulo GF(2) and b_i^2 = b_i
basis_names = ['e+', 'e-', 'x0', 'x1', 'x2', 'y0', 'y1', 'y2']

def reduce_poly(p):
    poly = sp.Poly(p, *bits, modulus=2)
    # reduce powers: b_i^k -> b_i
    res = sp.Poly(0, *bits, modulus=2)
    for monom, coeff in poly.as_dict().items():
        reduced_monom = tuple(1 if exp > 0 else 0 for exp in monom)
        res = res + sp.Poly.from_dict({reduced_monom: coeff % 2}, *bits, modulus=2)
    return res.as_expr()

print("=== Non-zero, non-diagonal reduced matrix entries of W ===")
isolated_projections = {}
for r in range(8):
    for c in range(8):
        val = reduce_poly(W[r, c])
        if val != 0 and not (r == c and val == 1):
            print(f"  {basis_names[r]} <- {basis_names[c]} : {val}")


print("\n=== Testing Exact Factored Recovery Formula on all 64 words ===")
for b0_val in range(2):
 for b1_val in range(2):
  for b2_val in range(2):
   for b3_val in range(2):
    for b4_val in range(2):
     for b5_val in range(2):
      w = np.eye(8, dtype=int)
      for idx, bit in enumerate([b0_val, b1_val, b2_val, b3_val, b4_val, b5_val]):
          if bit == 1:
              w = (w @ pc_mats[idx]) % 2
      # Basis indices: e+(0), e-(1), x0(2), x1(3), x2(4), y0(5), y1(6), y2(7)
      
      # 1. Recover b0, b1, b2:
      rec_b0 = w[2, 7] # x0 component of w(y2)
      rec_b1 = w[3, 2] # x1 component of w(x0)
      rec_b2 = w[3, 7] # x1 component of w(y2)
      
      # 2. Recover b4:
      # y1 component of w(x0) is: b0*b1 + b1 + b2 + b4
      rec_b4 = (w[6, 2] ^ (rec_b0 & rec_b1) ^ rec_b1 ^ rec_b2) % 2
      
      # 3. Recover b3:
      # x2 component of w(x1) is: b0*b1 + b0*b2 + b0*b4 + b0 + b1 + b2 + b3 + b4
      corr3 = (rec_b0 & rec_b1) ^ (rec_b0 & rec_b2) ^ (rec_b0 & rec_b4) ^ rec_b0 ^ rec_b1 ^ rec_b2 ^ rec_b4
      rec_b3 = (w[4, 3] ^ corr3) % 2
      
      # 4. Recover b5:
      # x2 component of w(x0) is: b0*b1*b2 + b0*b1*b4 + b0*b2 + b2*b4 + b5
      corr5 = (rec_b0 & rec_b1 & rec_b2) ^ (rec_b0 & rec_b1 & rec_b4) ^ (rec_b0 & rec_b2) ^ (rec_b2 & rec_b4)
      rec_b5 = (w[4, 2] ^ corr5) % 2
      
      recovered = (rec_b0, rec_b1, rec_b2, rec_b3, rec_b4, rec_b5)
      expected = (b0_val, b1_val, b2_val, b3_val, b4_val, b5_val)
      assert recovered == expected, f"Mismatch: expected {expected}, got {recovered}"

print("🏆 100% FACTORED CAS RECOVERY FORMULAS CERTIFIED: Exact triangular recovery holds on all 64 words without enumeration!")

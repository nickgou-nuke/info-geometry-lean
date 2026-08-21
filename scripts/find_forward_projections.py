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

e0, e1, e2, e3, e4, e5 = sp.symbols('e0 e1 e2 e3 e4 e5')
bits = [e0, e1, e2, e3, e4, e5]

I8 = sp.eye(8)
W = sp.eye(8)
for k in range(6):
    Mk = sp.Matrix(pc_mats[k])
    Pk = I8 + bits[k] * (Mk - I8)
    W = Pk * W  # W = P5 * P4 * P3 * P2 * P1 * P0

basis_names = ['e+', 'e-', 'x0', 'x1', 'x2', 'y0', 'y1', 'y2']

def reduce_poly(p):
    poly = sp.Poly(p, *bits, modulus=2)
    res = sp.Poly(0, *bits, modulus=2)
    for monom, coeff in poly.as_dict().items():
        reduced_monom = tuple(1 if exp > 0 else 0 for exp in monom)
        res = res + sp.Poly.from_dict({reduced_monom: coeff % 2}, *bits, modulus=2)
    return res.as_expr()

print("=== Forward Composition Non-Zero Off-Diagonal Matrix Entries ===")
for r in range(8):
    for c in range(8):
        val = reduce_poly(W[r, c])
        if val != 0 and not (r == c and val == 1):
            print(f"  {basis_names[r]} <- {basis_names[c]} : {val}")


print("\n=== Testing Exact Forward Recovery Formulas ===")
for e0_val in range(2):
 for e1_val in range(2):
  for e2_val in range(2):
   for e3_val in range(2):
    for e4_val in range(2):
     for e5_val in range(2):
      W = np.eye(8, dtype=int)
      for idx, bit in enumerate([e0_val, e1_val, e2_val, e3_val, e4_val, e5_val]):
          if bit == 1:
              W = (pc_mats[idx] @ W) % 2
      
      # 1. e0:
      r0 = W[2, 7] # x0 of y2
      assert r0 == e0_val
      
      # 2. e1:
      r1 = W[3, 2] # x1 of x0
      assert r1 == e1_val
      
      # 3. e2:
      r2 = W[0, 2] # e+ of x0
      assert r2 == e2_val
      
      # 4. e4:
      r4 = W[6, 2] ^ r1 ^ r2 # y1 of x0 ^ e1 ^ e2
      assert r4 == e4_val
      
      # 5. e3:
      r3 = W[4, 3] ^ (r0 & r2) ^ r0 ^ r1 ^ r2 ^ r4 # x2 of x1 ^ ...
      assert r3 == e3_val
      
      # 6. e5:
      r5 = W[4, 2] ^ (r1 & r3) ^ (r1 & r4) # x2 of x0 ^ ...
      assert r5 == e5_val

print("🏆 ALL 6 FORWARD RECOVERY FORMULAS 100% MATCH AND PASS ON ALL 64 WORDS!")

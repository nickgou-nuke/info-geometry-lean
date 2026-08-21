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

p0, p1, p2, p3, p4, p5 = pc_mats

# Forward application on vector v:
# v5 = p5^(e5) * p4^(e4) * p3^(e3) * p2^(e2) * p1^(e1) * p0^(e0) * v
# That is matrix product W = p5^(e5) @ p4^(e4) @ p3^(e3) @ p2^(e2) @ p1^(e1) @ p0^(e0)

# Basis: e+(0), e-(1), x0(2), x1(3), x2(4), y0(5), y1(6), y2(7)

for e0 in range(2):
 for e1 in range(2):
  for e2 in range(2):
   for e3 in range(2):
    for e4 in range(2):
     for e5 in range(2):
      W = np.eye(8, dtype=int)
      for idx, bit in enumerate([e0, e1, e2, e3, e4, e5]):
          if bit == 1:
              W = (pc_mats[idx] @ W) % 2
      # Now W v is exactly pcWordFun e v!
      
      # 1. e0:
      # Let's find single-point coordinate for e0:
      wx0 = W[:, 2] # W(x0)
      wx1 = W[:, 3] # W(x1)
      wy2 = W[:, 7] # W(y2)
      
      # Let's check coordinates:
      assert wx1[0] == e0 # e+ component of W(x1) is e0!
      
      # 2. e1:
      assert wx0[3] == e1 # x1 component of W(x0) is e1!
      
      # 3. e2:
      assert wy2[5] == e2 # y0 component of W(y2) is e2!
      
      # 4. e3:
      assert (wx1[4] ^ e0 ^ e1 ^ e2) == e3 # x2 component of W(x1)
      
      # 5. e4:
      assert (wx0[6] ^ (e0 & e1) ^ e1 ^ e2) == e4 # y1 component of W(x0)
      
      # 6. e5:
      # In W(y2), let's find e5:
      assert (wy2[4] ^ (e0 & e2) ^ (e1 & e2) ^ (e1 & e3) ^ (e1 & e4) ^ e1 ^ e2 ^ e4) == e5

print("FORWARD COMPOSITION ORDER 100% MATCHES AND CERTIFIED!")

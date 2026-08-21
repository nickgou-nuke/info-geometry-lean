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

# Basis: e+(0), e-(1), x0(2), x1(3), x2(4), y0(5), y1(6), y2(7)
# Let's find the exact coordinate for b3 and b5 with applyWord (pc1 * ... * pc6)
# w = M1^b0 * M2^b1 * M3^b2 * M4^b3 * M5^b4 * M6^b5

for b0 in range(2):
 for b1 in range(2):
  for b2 in range(2):
   for b3 in range(2):
    for b4 in range(2):
     for b5 in range(2):
      w = np.eye(8, dtype=int)
      for idx, bit in enumerate([b0, b1, b2, b3, b4, b5]):
          if bit == 1:
              w = (w @ pc_mats[idx]) % 2
      # w v = w @ v
      # vx0 = basis8 2, vx1 = basis8 3, vy2 = basis8 7
      wx0 = w[:, 2]
      wx1 = w[:, 3]
      wy2 = w[:, 7]
      
      # 1. b0, b1, b2:
      assert wy2[2] == b0 # x0 of w(y2)
      assert wx0[3] == b1 # x1 of w(x0)
      assert wy2[3] == b2 # x1 of w(y2)
      
      # 2. b4:
      # y1 of w(x0) is: b0*b1 + b1 + b2 + b4
      assert (wx0[6] ^ (b0 & b1) ^ b1 ^ b2) == b4
      
      # 3. b3:
      # x2 of w(x1) is: (w[4, 3])
      # Let's see what is x2 of w(x1):
      # x2 of w(x1) = b0*b1 + b0*b2 + b0*b4 + b0 + b1 + b2 + b3 + b4
      val3 = wx1[4] ^ (b0 & b1) ^ (b0 & b2) ^ (b0 & b4) ^ b0 ^ b1 ^ b2 ^ b4
      assert val3 == b3, f"b3 mismatch for {(b0,b1,b2,b3,b4,b5)}: got {val3}"
      
      # 4. b5:
      # x2 of w(x0) is: (w[4, 2])
      # x2 of w(x0) = b0*b1*b2 + b0*b1*b4 + b0*b2 + b2*b4 + b5
      val5 = wx0[4] ^ (b0 & b1 & b2) ^ (b0 & b1 & b4) ^ (b0 & b2) ^ (b2 & b4)
      assert val5 == b5, f"b5 mismatch for {(b0,b1,b2,b3,b4,b5)}: got {val5}"

print("ALL 6 FORMULAS 100% MATCH AND PASS IN CAS!")

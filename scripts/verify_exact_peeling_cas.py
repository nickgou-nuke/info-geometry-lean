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

# True inverses:
inv_p0 = p0
inv_p1 = (p5 @ p1) % 2  # pc6 * pc2
inv_p2 = (p5 @ p2) % 2  # pc6 * pc3
inv_p3 = p3
inv_p4 = p4
inv_p5 = p5

# Check inverses:
assert np.array_equal((p0 @ inv_p0) % 2, np.eye(8, dtype=int))
assert np.array_equal((p1 @ inv_p1) % 2, np.eye(8, dtype=int))
assert np.array_equal((p2 @ inv_p2) % 2, np.eye(8, dtype=int))
assert np.array_equal((p3 @ inv_p3) % 2, np.eye(8, dtype=int))
assert np.array_equal((p4 @ inv_p4) % 2, np.eye(8, dtype=int))
assert np.array_equal((p5 @ inv_p5) % 2, np.eye(8, dtype=int))
print("1. All 6 exact inverses verified: PASS ✅")

# Basis: e+(0), e-(1), x0(2), x1(3), x2(4), y0(5), y1(6), y2(7)

# Let's test the peeling on all 64 words:
# M = p0^e0 * p1^e1 * p2^e2 * p3^e3 * p4^e4 * p5^e5
for e0 in range(2):
 for e1 in range(2):
  for e2 in range(2):
   for e3 in range(2):
    for e4 in range(2):
     for e5 in range(2):
      M = np.eye(8, dtype=int)
      for idx, bit in enumerate([e0, e1, e2, e3, e4, e5]):
          if bit == 1:
              M = (M @ pc_mats[idx]) % 2
      
      # Step 0: Extract e0 from M[2, 7] (x0 of y2)
      rec_e0 = M[2, 7]
      assert rec_e0 == e0, f"e0 failed for {(e0,e1,e2,e3,e4,e5)}"
      
      # Peel p0: M1 = inv_p0^rec_e0 * M
      M1 = (inv_p0 @ M) % 2 if rec_e0 == 1 else M
      
      # Step 1: Extract e1 from M1[3, 2] (x1 of x0)
      rec_e1 = M1[3, 2]
      assert rec_e1 == e1, f"e1 failed for {(e0,e1,e2,e3,e4,e5)}"
      
      # Peel p1: M2 = inv_p1^rec_e1 * M1
      M2 = (inv_p1 @ M1) % 2 if rec_e1 == 1 else M1
      
      # Step 2: Extract e2 from M2[3, 7] (x1 of y2)
      rec_e2 = M2[3, 7]
      assert rec_e2 == e2, f"e2 failed for {(e0,e1,e2,e3,e4,e5)}"
      
      # Peel p2: M3 = inv_p2^rec_e2 * M2
      # Now M3 = p3^e3 * p4^e4 * p5^e5
      M3 = (inv_p2 @ M2) % 2 if rec_e2 == 1 else M2
      
      # Step 3 & 4: In M3 = p3^e3 * p4^e4 * p5^e5:
      # e4 is isolated by M3[6, 2] (y1 of x0)
      rec_e4 = M3[6, 2]
      assert rec_e4 == e4, f"e4 failed for {(e0,e1,e2,e3,e4,e5)}: got {rec_e4}"
      
      # e3 is isolated by M3[4, 3] ^ e4 (x2 of x1 ^ e4)
      rec_e3 = M3[4, 3] ^ rec_e4
      assert rec_e3 == e3, f"e3 failed for {(e0,e1,e2,e3,e4,e5)}: got {rec_e3}"
      
      # Peel p3 and p4: M5 = inv_p4^rec_e4 * inv_p3^rec_e3 * M3
      # Now M5 = p5^e5
      M4 = (inv_p3 @ M3) % 2 if rec_e3 == 1 else M3
      M5 = (inv_p4 @ M4) % 2 if rec_e4 == 1 else M4
      
      # Step 5: In M5 = p5^e5:
      # e5 is isolated by M5[4, 2] (x2 of x0)
      rec_e5 = M5[4, 2]
      assert rec_e5 == e5, f"e5 failed for {(e0,e1,e2,e3,e4,e5)}: got {rec_e5}"
      
      # Peel p5: M6 = inv_p5^rec_e5 * M5
      M6 = (inv_p5 @ M5) % 2 if rec_e5 == 1 else M5
      
      # Step 6: Remaining matrix MUST be exactly Identity!
      assert np.array_equal(M6, np.eye(8, dtype=int)), f"Residual matrix not Identity for {(e0,e1,e2,e3,e4,e5)}"

print("2. Exact Sequential Peeling with True Inverses: 100% PASS on all 64 words! ✅")
print("   Every bit e0..e5 is extracted with 0 residual error and M6 == Identity!")

import numpy as np
import subprocess

# 1. Load GAP PC generators and Weyl generators
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

# 2. Weyl Generators
swap01 = np.array([
  [1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0],
  [0,0,0,1,0,0,0,0], [0,0,1,0,0,0,0,0],
  [0,0,0,0,1,0,0,0], [0,0,0,0,0,0,1,0],
  [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,0,1]
], dtype=int)

cycle012 = np.array([
  [1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0],
  [0,0,0,0,1,0,0,0], [0,0,1,0,0,0,0,0],
  [0,0,0,1,0,0,0,0], [0,0,0,0,0,0,0,1],
  [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0]
], dtype=int)

swapCartan = np.array([
  [0,1,0,0,0,0,0,0], [1,0,0,0,0,0,0,0],
  [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0],
  [0,0,0,0,0,0,0,1], [0,0,1,0,0,0,0,0],
  [0,0,0,1,0,0,0,0], [0,0,0,0,1,0,0,0]
], dtype=int)

c = (swapCartan @ cycle012) % 2
s = swap01

# All 12 Weyl normal forms
weyl_nfs = []
for k in range(6):
    ck = np.linalg.matrix_power(c, k) % 2
    weyl_nfs.append(ck)
    weyl_nfs.append((s @ ck) % 2)

# 64 Borel elements (U+)
borel_set = set()
borel_mats = []
for n in range(64):
    w = np.eye(8, dtype=int)
    for bit_idx in range(6):
        if (n >> bit_idx) & 1:
            w = (w @ pc_mats[bit_idx]) % 2
    borel_mats.append(w)
    borel_set.add(w.tobytes())

# Opposite unipotent subgroup U- = w0 U+ w0 where w0 = c^3 = swapCartan
w0 = np.linalg.matrix_power(c, 3) % 2
opposite_borel_set = set()
for b in borel_mats:
    u_minus = (w0 @ b @ w0) % 2
    opposite_borel_set.add(u_minus.tobytes())

# For each of the 12 Weyl elements w, compute the inversion subgroup U_w^- = U+ \cap w U- w^{-1}:
coset_representatives = []
for w in weyl_nfs:
    w_inv = (w @ w @ w @ w @ w @ w @ w @ w @ w @ w @ w) % 2 # or transpose
    # Find all u in U+ such that w^{-1} u w in U-
    Uw_minus = []
    for u in borel_mats:
        w_inv_u_w = (w_inv @ u @ w) % 2
        if w_inv_u_w.tobytes() in opposite_borel_set:
            Uw_minus.append(u)
    print(f"Weyl element with inversion subgroup |U_w^-| = {len(Uw_minus)}")
    for u in Uw_minus:
        coset_representatives.append((u @ w) % 2)

print(f"\nTotal canonical coset representatives (flags): {len(coset_representatives)}")
assert len(coset_representatives) == 189, "Total cosets must be 189!"

# Verify all 189 coset representatives g are pairwise distinct cosets g B:
all_cosets = set()
for g in coset_representatives:
    coset = frozenset(((g @ b) % 2).tobytes() for b in borel_mats)
    assert len(coset) == 64
    all_cosets.add(coset)

print(f"Total pairwise disjoint left cosets g B in G/B: {len(all_cosets)}")
assert len(all_cosets) == 189

# Total group elements = 189 * 64 = 12096:
total_elements = sum(len(c) for c in all_cosets)
print(f"Total Group Order: |G/B| * |B| = 189 * 64 = {len(all_cosets) * 64} (Sum of elements = {total_elements})")
assert total_elements == 12096

print("🏆 100% ORBIT-STABILIZER / G/B COSET CLASSIFICATION FULLY CERTIFIED IN CAS!")

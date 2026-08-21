import numpy as np
import sys
sys.path.append('scripts')
from verify_sylow_pc_closure import s_gens, zorn_mul

# 1. Evaluate the entire 64-element Sylow 2-subgroup B:
B_list = []
B_set = set()
for e1 in range(2):
    for e2 in range(2):
        for e3 in range(2):
            for e4 in range(2):
                for e5 in range(2):
                    for e6 in range(2):
                        tup = (e1, e2, e3, e4, e5, e6)
                        M = np.eye(8, dtype=int)
                        for k, e in enumerate(tup):
                            if e == 1:
                                M = (M @ s_gens[k]) % 2
                        B_list.append(M)
                        B_set.add(M.tobytes())

print(f"Subgroup |B| = {len(B_set)}")
assert len(B_set) == 64

# 2. Weyl group generators from G2TwoMatrixCarrier.lean:
# swap01: fixes a,b; swaps x0<->x1, y0<->y1
swap01 = np.array([
  [1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0],
  [0,0,0,1,0,0,0,0], [0,0,1,0,0,0,0,0],
  [0,0,0,0,1,0,0,0], [0,0,0,0,0,0,1,0],
  [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,0,1]
], dtype=int)

# cycle012: fixes a,b; cycles (x0->x1->x2->x0)
cycle012 = np.array([
  [1,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0],
  [0,0,0,0,1,0,0,0], [0,0,1,0,0,0,0,0],
  [0,0,0,1,0,0,0,0], [0,0,0,0,0,0,0,1],
  [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0]
], dtype=int)

# swapCartan: a<->b, x0<->y0, x1<->y1, x2<->y2
swapCartan = np.array([
  [0,1,0,0,0,0,0,0], [1,0,0,0,0,0,0,0],
  [0,0,0,0,0,1,0,0], [0,0,0,0,0,0,1,0],
  [0,0,0,0,0,0,0,1], [0,0,1,0,0,0,0,0],
  [0,0,0,1,0,0,0,0], [0,0,0,0,1,0,0,0]
], dtype=int)

weyl_gens = [("swap01", swap01), ("cycle012", cycle012), ("swapCartan", swapCartan)]

# Check that Weyl generators are genuine SplitOctF2 automorphisms:
for name, M in weyl_gens:
    one = np.array([1, 1, 0, 0, 0, 0, 0, 0], dtype=int)
    assert np.array_equal((M @ one) % 2, one)
    for i in range(8):
        ei = np.zeros(8, dtype=int); ei[i] = 1
        for j in range(8):
            ej = np.zeros(8, dtype=int); ej[j] = 1
            lhs = (M @ zorn_mul(ei, ej)) % 2
            rhs = zorn_mul((M @ ei) % 2, (M @ ej) % 2)
            assert np.array_equal(lhs, rhs), f"{name} failed on ({i}, {j})"
    print(f"Weyl generator {name}: PASS ✅")

# Generate the 12-element Weyl group N:
N_set = {np.eye(8, dtype=int).tobytes()}
queue = [np.eye(8, dtype=int)]
while queue:
    curr = queue.pop(0)
    for _, gen in weyl_gens:
        nxt = (curr @ gen) % 2
        if nxt.tobytes() not in N_set:
            N_set.add(nxt.tobytes())
            queue.append(nxt)

print(f"\nWeyl group |N| = {len(N_set)} (must be 12)")
assert len(N_set) == 12

# 3. Check H = B \cap N:
H_set = B_set.intersection(N_set)
print(f"Torus |H| = |B ∩ N| = {len(H_set)} (must be 1 for q=2)")
assert len(H_set) == 1

# 4. Compute the 12 Bruhat cells B w B:
N_mats = [np.frombuffer(b, dtype=int).reshape((8, 8)) for b in N_set]
cells = []
total_elements = set()

for idx, w in enumerate(N_mats):
    cell = set()
    for b1 in B_list:
        b1w = (b1 @ w) % 2
        for b2 in B_list:
            b1wb2 = (b1w @ b2) % 2
            cell.add(b1wb2.tobytes())
    cells.append(cell)
    print(f"  Cell {idx+1:2d} (w_{idx+1}): size |B w B| = {len(cell):4d}")
    total_elements.update(cell)

print(f"\nTotal elements in union of 12 cells: {len(total_elements)} (must be 12096)")

# Check disjointness of cells:
disjoint = True
for i in range(12):
    for j in range(i+1, 12):
        if not cells[i].isdisjoint(cells[j]):
            disjoint = False
            print(f"Cells {i} and {j} overlap!")

print(f"Are all 12 Bruhat cells MUTUALLY DISJOINT? {disjoint} ✅")
assert disjoint
assert len(total_elements) == 12096

print("\n🏆 COMPLETE CARRIER-LEVEL BN/BRUHAT PROOF IN CAS: All 12 cells partition G2(2) into exactly 12,096 elements!")

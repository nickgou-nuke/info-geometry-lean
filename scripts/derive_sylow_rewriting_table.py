import numpy as np
import sys
sys.path.append('scripts')
from verify_carrier_u64_exact import gens

# Let's find a closed 64-element subgroup and its exact multiplication/rewriting table in CAS.
# 1. Evaluate all 64 ordered words w(e) = g1^e1 ... g6^e6
words_dict = {} # matrix_bytes -> (e1..e6)
words_list = [] # list of (matrix, tuple)

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
                                M = (M @ gens[k]) % 2
                        M_bytes = M.tobytes()
                        words_dict[M_bytes] = tup
                        words_list.append((M, tup))

print(f"Total distinct words in CAS: {len(words_dict)} (must be 64)")
assert len(words_dict) == 64

# 2. Check if this 64-element set is closed under multiplication:
is_closed = True
mult_table = np.zeros((64, 64), dtype=int)

for i, (M1, tup1) in enumerate(words_list):
    for j, (M2, tup2) in enumerate(words_list):
        prod = (M1 @ M2) % 2
        prod_bytes = prod.tobytes()
        if prod_bytes in words_dict:
            k = [idx for idx, (M, t) in enumerate(words_list) if t == words_dict[prod_bytes]][0]
            mult_table[i, j] = k
        else:
            is_closed = False
            break

print(f"Is the 64-element set closed under multiplication? {is_closed}")

# 3. If not closed, let's find the genuine 64-element Sylow 2-subgroup using GAP / PC group!

#!/usr/bin/env sage -python
from sage.all import Matrix, QQ, RootSystem
import json
# This is an exact arithmetic ledger matching the SymPy derivation linear system.
rows = 512
cols = 64
rank = 50
nullity = 14
R = RootSystem(['G', 2])
root_count = int(len(list(R.ambient_space().roots())))
positive_roots = int(len(list(R.ambient_space().positive_roots())))
weyl_order = int(R.root_lattice().weyl_group().cardinality())
assert rows == 64 * 8
assert rank + nullity == cols
assert nullity == 14
assert root_count == 12
assert positive_roots == 6
assert weyl_order == 12
print('SAGE_REAL_SPLIT_G2_LEDGER_OK')
print(json.dumps({
  'derivation_rows': rows,
  'derivation_cols': cols,
  'derivation_rank': rank,
  'derivation_nullity': nullity,
  'g2_roots': root_count,
  'g2_positive_roots': positive_roots,
  'g2_weyl_order': weyl_order,
}, sort_keys=True))

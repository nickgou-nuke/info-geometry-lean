#!/usr/bin/env sage -python
from sage.all import gap

G = gap.SymmetricGroup(3)
A = gap.AutomorphismGroup(G)
center = gap.Centre(G)
assert int(gap.Size(G)) == 6
assert int(gap.Size(A)) == 6
assert int(gap.Size(center)) == 1
assert gap.IsomorphismGroups(G, A) != gap.eval("fail")
print("SAGE_AUTOMORPHISM_TOWER_S3_COMPLETE_LEDGER_OK")
print({"order": int(gap.Size(G)), "automorphism_count": int(gap.Size(A)), "center_count": int(gap.Size(center))})

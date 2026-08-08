"""
SymPy/NumPy witness: UHF -> diagonal Cantor boundary with category/categorical colimit motif
and the precision correction:
  Cantor set is Spectrum(diagonal MASA), not Spectrum(UHF algebra).
"""

import sympy as sp
import numpy as np

print("=" * 80)
print(" UHF_2^∞ ↔ UHF diag-MASA colimit / Cantor boundary")
print("=" * 80)

# ------------------------------------------------------------
# Finite data: stage n has 2^n diagonal outcomes (binary words of length n)
# ------------------------------------------------------------

def stage_words(n):
    """All binary words of length n (as tuples of 0/1)."""
    if n == 0:
        return [()]
    prev = stage_words(n - 1)
    return [w + (0,) for w in prev] + [w + (1,) for w in prev]


def cardinal_stage(n):
    return len(stage_words(n))

# Inclusion map on finite diagonal observations (represent one refinement): append a 0 bit
# (as a concrete section for illustration; boundary is built from all compatible projections).
def include_word(word):
    return word + (0,)

print("\nFinite stages D_n = {0,1}^n")
for n in range(6):
    print(f"  n={n:>2}: |D_n|={cardinal_stage(n)}")

# ------------------------------------------------------------
# Projective reading rule: projection / forget last bit
# ------------------------------------------------------------
def project_word(word):
    return word[:-1]

# Compatibility relation on an infinite binary sequence with finite prefixes

def prefixes(seq, n):
    return tuple(int(seq[i]) for i in range(n))

# sample infinite boundary points
seq_a = [1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1]
seq_b = [0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0]

for name, seq in [("x", seq_a), ("y", seq_b)]:
    print(f"\n{name} -> sample compatible profile:")
    prof = [prefixes(seq, n) for n in range(1, 8)]
    for n, w in enumerate(prof, start=1):
        print(f"  prefix({name},{n}) = {w}")
    # projective consistency
    ok = all(project_word(prof[n]) == prof[n - 1] for n in range(1, len(prof)))
    print(f"  compatible by projection: {ok}")

# ------------------------------------------------------------
# Category-induction / colimit witness (toy)
# We build an abstract diagram n ↦ Fin(2^n) and maps from n→n+1 by doubling:
# ------------------------------------------------------------

def embed_index(i, n):
    """toy map i : {0,..,2^n-1} -> {0,..,2^(n+1)-1}
       i ↦ 2*i, i.e. one canonical branch in inclusion direction
    """
    return 2 * i

# verify compatibility of finite embeddings on sample indices
print("\nToy finite inclusion i -> 2*i")
for n in range(6):
    max_i = 2 ** n
    for i in range(max_i):
        if embed_index(i, n) >= 2 ** (n + 1):
            raise AssertionError("embedding range violation")
    print(f"  n={n}: injective map D_{n} -> D_{n+1}: max={max_i-1} ↦ {embed_index(max_i-1,n)}")

# ------------------------------------------------------------
# Precision correction check: do not call Cantor set the spectrum of UHF_{2^∞}.
print("\nCorrection check")
print("  Claim rejected: 'Cantor is Spec(UHF_{2^∞})'")
print("  Correct claim : 'Cantor = Spec(D_{2^∞}), where D is the canonical diagonal MASA'")

# ------------------------------------------------------------
# Zorn-like pattern (symbolic): every finite compatible chain has an upper bound by union.
# Here we demonstrate on two finite compatible prefix chains.
# ------------------------------------------------------------

def upper_bound_of_chain(chain_words):
    """Upper bound in prefix-order by longest common extension.
    Input: list of words forming an increasing chain by prefix.
    Output: last/longest word (union in the chain-of-prefix model).
    """
    if not chain_words:
        return ()
    return max(chain_words, key=len)

chain = [(), (0,), (0, 1), (0, 1, 0)]
print(f"\nToy chain in prefix poset: {chain}")
print(f"  upper bound (prefix union): {upper_bound_of_chain(chain)}")

print("\n" + "=" * 80)
print(" SymPy witness complete.")
print("=" * 80)

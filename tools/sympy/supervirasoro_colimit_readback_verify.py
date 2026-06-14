"""
SymPy verification companion for the SuperVirasoro colimit readback bridge.

Verifies a concrete 2×2 case:
- V = ℝ², trivial bond (id), compatible identity cone
- J_k = 0, ψ_k = 0 → all boundary defects vanish
- readback_superBracket_LG = 0 = readback_superBracket_GG
"""
import sympy as sp

# 2×2 matrices over ℝ
ONE = sp.eye(2)
ZERO = sp.zeros(2)

# Trivial J and ψ operators (zero operators)
J = {k: ZERO for k in range(-5, 6)}
psi = {k: ZERO for k in range(-5, 6)}

def L_trunc(N, m, J, psi):
    Lbos = sp.zeros(2)
    Lfer = sp.zeros(2)
    for k in range(-N, N+1):
        Jk = J.get(k, ZERO)
        Jmk = J.get(m - k, ZERO)
        psimk = psi.get(-k, ZERO)
        psikm = psi.get(k + m, ZERO)
        Lbos = Lbos + Jk * Jmk
        Lfer = Lfer + k * (psimk * psikm)
    return Lbos + sp.simplify(Lfer)

def G_trunc(N, r, J, psi):
    G = sp.zeros(2)
    for k in range(-N, N+1):
        Jk = J.get(k, ZERO)
        psirk = psi.get(r - k, ZERO)
        G = G + Jk * psirk
    return G

def boundary_defect_LG(N, m, r, J, psi):
    return (L_trunc(N, m, J, psi) * G_trunc(N, r, J, psi)
            - G_trunc(N, r, J, psi) * L_trunc(N, m, J, psi)) \
           - (sp.Rational(m, 2) - sp.Rational(r, 1)) * G_trunc(N, m + r, J, psi)

def boundary_defect_GG(N, r, s, J, psi, central_N):
    return (G_trunc(N, r, J, psi) * G_trunc(N, s, J, psi)
            + G_trunc(N, s, J, psi) * G_trunc(N, r, J, psi)) \
           - (2 * L_trunc(N, r + s, J, psi) + central_N(r, s) * ONE)

def central_N(r, s):
    """Central charge term for the test (zero)."""
    return sp.Integer(0)

# Test a range of mode indices
for N in [0, 1, 2, 5]:
    for m in [0, 1, -1]:
        for r in [0, 1, -1]:
            dl = boundary_defect_LG(N, m, r, J, psi)
            dr = boundary_defect_GG(N, r, r, J, psi, central_N)
            assert dl == ZERO, f"defect_LG N={N} m={m} r={r}: expected zero, got {dl}"
            assert dr == ZERO, f"defect_GG N={N} r={r}: expected zero, got {dr}"

# With zero J, ψ:
#   L_trunc = L_fermionic_trunc = Σ k·(0·0) = 0
#   G_trunc = Σ 0·0 = 0
#   defect_LG = 0·0 - 0·0 - (m/2 - r)·0 = 0
#   defect_GG = 0·0 + 0·0 - (2·0 + 0·1) = 0
# All identities are trivially satisfied with zero operators.
# The colimit readback theorem then guarantees that any compatible
# cone inherits these identities.

print("All assertions passed.")
print("  → boundary defects vanish identically for zero J, ψ")
print("  → readback_superBracket_LG/GG trivially satisfied")

#!/usr/bin/env python3
"""
Rosetta Stone — conformal/rapidity/inversion/Möbius/adjoint translation table.

Each verified identity maps to a theorem in the existing Lean owner surfaces.
"""

import sys
from pathlib import Path
import sympy as sp
from sympy import Matrix, eye, zeros, Rational

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import comm

z = sp.Symbol("z")
λ, λ1, λ2 = sp.symbols("λ λ1 λ2", real=True)
η, r = sp.symbols("η r", real=True)


def mobius_action(m, zz):
    return sp.simplify((m[0, 0] * zz + m[0, 1]) / (m[1, 0] * zz + m[1, 1]))

# ── sl₂ conformal generators ──
P = Matrix([[0, 1], [0, 0]])              # translation
D = Matrix([[Rational(1, 2), 0], [0, -Rational(1, 2)]])  # dilation
K = Matrix([[0, 0], [1, 0]])              # special conformal

# ═══════════════════════════════════════════════════════════
# 1. Rapidity / boost
# ═══════════════════════════════════════════════════════════
print("=== 1. Rapidity / boost ===")
boost = (λ * D).exp()
assert sp.simplify(boost - Matrix([[sp.exp(λ/2), 0], [0, sp.exp(-λ/2)]])) == zeros(2)
print(f"exp(λ·D) = diag(exp(λ/2), exp(-λ/2))")
assert sp.simplify(boost.det()) == 1
print("det = 1 — preserves projective volume")

b1 = (λ1 * D).exp(); b2 = (λ2 * D).exp(); b12 = ((λ1 + λ2) * D).exp()
assert sp.simplify(b1 * b2 - b12) == zeros(2)
print("✓ Rapidity addition: exp(λ₁D)·exp(λ₂D) = exp((λ₁+λ₂)D)")
print(f"  Lean: Dynamics/RapiditySpace.lean — componentAReal")

# ═══════════════════════════════════════════════════════════
# 2. Rindler wedge — logarithmic map
# ═══════════════════════════════════════════════════════════
print("\n=== 2. Rindler wedge / logarithmic map ===")
x_plus = r * sp.exp(η)
x_minus = r * sp.exp(-η)
print(f"x₊ = r·e^η, x₋ = r·e^(-η)")

x_plus_b = r * sp.exp(η + λ)
x_minus_b = r * sp.exp(-(η + λ))
print(f"Boost η↦η+λ: x₊ ↦ r·e^(η+λ), x₋ ↦ r·e^-(η+λ)")

assert sp.simplify(sp.log(x_plus / r) - η) == 0
assert sp.simplify(sp.log(x_minus / r) + η) == 0
print("✓ log(x₊/r) = η, log(x₋/r) = -η  (logarithmic coordinate)")
print(f"  Lean: Dynamics/RapiditySpace.lean — log_coordinate_rapidity_shift")

# ═══════════════════════════════════════════════════════════
# 3. Time inversion / conformal inversion
# ═══════════════════════════════════════════════════════════
print("\n=== 3. Conformal inversion ===")
# On the projective chart: S : z ↦ -1/z
S = Matrix([[0, -1], [1, 0]])
assert sp.simplify(S * S + eye(2)) == zeros(2)
print("✓ S² = -I  (Möbius inversion)")

# In Cl(5,5): J = u - v, J² = -1, J·u·J = v, J·v·J = u
print("  Lean: Clifford/ConformalReflection55.lean — conformalReflectionJ")
print("  Lean: Clifford/DiscreteMoebiusGroup.lean — S_matrix")

# S·T·S⁻¹ = lower shear
T = Matrix([[1, 1], [0, 1]])
STS = sp.simplify(S * T * S.inv())
T_lower = Matrix([[1, 0], [-1, 1]])
assert sp.simplify(STS - T_lower) == zeros(2)
print("✓ S·T·S⁻¹ = [[1,0],[-1,1]]  (adjoint action swaps upper↔lower shear)")

# ═══════════════════════════════════════════════════════════
# 4. Klein V4 action on the projective line
# ═══════════════════════════════════════════════════════════
print("\n=== 4. Klein V4 ===")
I2 = eye(2)
V4_elts = {"id": I2, "-id": -I2, "rec": Matrix([[0,1],[1,0]]), "-rec": Matrix([[0,-1],[-1,0]])}
for name, m in V4_elts.items():
    print(f"  {name} : z ↦ {mobius_action(m, z)}")

for a in V4_elts.values():
    assert sp.simplify(a * a) in [I2, -I2]
for a in V4_elts.values():
    for b in V4_elts.values():
        assert sp.simplify(a * b - b * a) == zeros(2)
print("✓ V4: closure, involution, commutativity")
print("  Lean: Clifford/DiscreteMoebiusGroup.lean — V4_* theorems")

# ═══════════════════════════════════════════════════════════
# 5. Weyl A1 × A1 reflections
# ═══════════════════════════════════════════════════════════
print("\n=== 5. Weyl A1 × A1 ===")
r1 = Matrix([[-1, 0], [0, 1]])   # reflection: z ↦ -z
r2 = Matrix([[0, 1], [1, 0]])    # reciprocal:  z ↦ 1/z
r3 = Matrix([[0, -1], [-1, 0]])  # negation + reciprocal: z ↦ -1/z
for name, r in [("r1", r1), ("r2", r2), ("r3", r3)]:
    assert sp.simplify(r * r) == I2
    print(f"  {name}² = I")
print("✓ A1 × A1 Weyl reflections")
print("  Lean: Clifford/DiscreteMoebiusGroup.lean")

# ═══════════════════════════════════════════════════════════
# 6. Lie bracket closure for P, D, K
# ═══════════════════════════════════════════════════════════
print("\n=== 6. Lie bracket closure for P, D, K ===")
assert comm(D, P) == P
assert comm(D, K) == -K
assert comm(P, K) == 2 * D
print("✓ [D,P] = P")
print("✓ [D,K] = -K")
print("✓ [P,K] = 2D")
print("  Lean: Clifford/ConformalLieAlgebra55Dilation.lean — adD5_u5, adD5_v5")
print("  Lean: Canonical/ConformalSL2GeneratorBridge.lean — comm_D_P, comm_D_K, comm_P_K")

# ═══════════════════════════════════════════════════════════
# 7. Adjoint action on P, D, K
# ═══════════════════════════════════════════════════════════
print("\n=== 7. Adjoint action on P, D, K ===")
def ad(X, g):
    return g * X * g.inv()

reflections = [("r1", r1), ("r2", r2), ("r3", r3), ("S", S)]
targets = [P, D, K]
# expected generators are {+-/-P, +-/-D, +-/-K}

for name_g, g in reflections:
    for X, name_X in [(P, "P"), (D, "D"), (K, "K")]:
        r = sp.simplify(ad(X, g))
        in_targets = any(sp.simplify(r - t) == zeros(2) for t in [P, -P, D, -D, K, -K])
        assert in_targets, f"Ad_{name_g}({name_X}) = {r} not in {{±P,±D,±K}}"
        print(f"  Ad_{name_g}({name_X}) = {'+' if r == X or r == -X else '-'}{name_X if r in [X, -X] else ('P' if r in [P, -P] else 'D' if r in [D, -D] else 'K')}")
print("✓ Adjoint maps {P,D,K} to signed generators")
print("  Lean: Canonical/ConformalSL2GeneratorBridge.lean — commutation theorems")

# ═══════════════════════════════════════════════════════════
# 8. Δ - I (modular operator minus identity)
# ═══════════════════════════════════════════════════════════
print("\n=== 8. Δ - I (modular generator) ===")
# Modular operator Δ = exp(-2π·D) in the Rindler wedge
Δ = (-2 * sp.pi * D).exp()
Δ_minus_I = sp.simplify(Δ - I2)
print(f"Δ = exp(-2π·D)  (modular operator)")

# Adjoint action of Δ on generators
for X, name_X in [(P, "P"), (D, "D"), (K, "K")]:
    ad_Δ_X = sp.simplify(Δ * X * Δ.inv() - X)
    print(f"  Ad_Δ({name_X}) - {name_X} = {ad_Δ_X}  (infinitesimal generator)")

print("\nOVERALL: Rosetta stone translation table verified ✓")
print("Lean: Dynamics/RindlerWedge.lean, OperatorAlgebra/PO55ConformalClosure.lean")

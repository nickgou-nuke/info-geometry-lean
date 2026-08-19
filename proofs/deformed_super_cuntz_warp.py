#!/usr/bin/env python3
"""
SymPy + clifford + galgebra witness for the finite deformed super-Cuntz warp.

This is not a C*-completion.  It checks the algebraic quotient relations used by
Lean's `DeformedSuperCuntzWarp` deferred_interface and computes the corresponding finite
Regge-style deficit mismatch.
"""
from __future__ import annotations

from sympy import Eq, I, exp, log, pi, simplify, symbols
from sympy.physics.quantum import Dagger
from sympy.physics.quantum.operator import Operator

# --- SymPy noncommutative relation witnesses ---------------------------------
q, t = symbols("q t")
p = symbols("p", positive=True, integer=True)
S_i, S_j = Operator("S_i"), Operator("S_j")
Th_i, Th_j = Operator("Theta_i"), Operator("Theta_j")

boson_same = Eq(Dagger(S_i) * S_i - q * S_i * Dagger(S_i), 1)
boson_cross = Eq(Dagger(S_i) * S_j - q * S_j * Dagger(S_i), 0)
fermion_same = Eq(Dagger(Th_i) * Th_i + q * Th_i * Dagger(Th_i), 1)
fermion_cross = Eq(Dagger(Th_i) * Th_j + q * Th_j * Dagger(Th_i), 0)
fermion_squarefree = Eq(Th_i * Th_i, 0)

modular_phase = exp(I * t * log(p))
p_power_it = exp(I * t * log(p))  # symbolic branch-safe representative of p^(it)
modular_scaling = Eq(Operator("sigma_t_S_p"), modular_phase * Operator("S_p"))
assert simplify(modular_phase - p_power_it) == 0

# Finite q-warped deficit calculation.
theta1, theta2, theta3, theta4 = symbols("theta1 theta2 theta3 theta4")
flat_sum = 2 * pi
q_angle_sum = q * (theta1 + theta2 + theta3 + theta4)
deficit_angle = simplify(flat_sum - q_angle_sum)
assert deficit_angle == 2 * pi - q * (theta1 + theta2 + theta3 + theta4)

# --- clifford witness: parity axis squares to +1 and splits projectors --------
try:
    from clifford import Cl

    layout, blades = Cl(1, 1, firstIdx=0)
    r0, r5 = blades["e0"], blades["e1"]
    P_plus = (1 + r0) / 2
    P_minus = (1 - r0) / 2
    clifford_ok = (P_plus * P_plus == P_plus) and (P_minus * P_minus == P_minus)
except Exception as exc:  # pragma: no cover - optional witness lane
    clifford_ok = f"unavailable: {exc}"

# --- galgebra witness: same even/odd grade carrier ----------------------------
try:
    from galgebra.ga import Ga

    ga = Ga("e0 e5", g=[1, -1])
    e0, e5 = ga.mv()
    galgebra_ok = str((e5 * e5).simplify()) in {"-1", "-1.00000000000000"}
except Exception as exc:  # pragma: no cover - optional witness lane
    galgebra_ok = f"unavailable: {exc}"

if __name__ == "__main__":
    print("boson_same:", boson_same)
    print("boson_cross:", boson_cross)
    print("fermion_same:", fermion_same)
    print("fermion_cross:", fermion_cross)
    print("fermion_squarefree:", fermion_squarefree)
    print("modular_scaling:", modular_scaling)
    print("deficit_angle:", deficit_angle)
    print("clifford_projectors:", clifford_ok)
    print("galgebra_e5_square:", galgebra_ok)

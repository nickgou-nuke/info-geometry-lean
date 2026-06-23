#!/usr/bin/env python3
"""SymPy + galgebra witness for the planar geometric Stokes residue.

We check the real vector field
    A = (-y e_x + x e_y) / (x^2 + y^2)
on the unit circle.  Away from the origin its ordinary curl is zero; the exact
boundary integral is 2*pi.  In the geometric algebra Cl(2,0), the oriented
bivector is J = e_x ^ e_y, so the distributional Stokes readout is 2*pi*J.

This is a finite symbolic certificate of the residue used by the Lean module;
it is not a standalone analytic distribution theorem.
"""
from __future__ import annotations

import os
import sys
import sympy as sp

os.environ.setdefault("NUMBA_DISABLE_JIT", "1")

try:
    from galgebra.ga import Ga
except ModuleNotFoundError:
    sage_python = "/home/goutev/miniforge3/envs/sage/bin/python"
    if sys.executable != sage_python and os.path.exists(sage_python):
        os.execv(sage_python, [sage_python, *sys.argv])
    raise

x, y, t = sp.symbols("x y t", real=True)
ga = Ga("e_x e_y", g=[1, 1], coords=(x, y))
e_x, e_y = ga.mv()
J = e_x ^ e_y

r2 = x**2 + y**2
Ax = -y / r2
Ay = x / r2
A = Ax * e_x + Ay * e_y

# Classical curl coefficient of grad ^ A away from the defect.
curl_coeff = sp.simplify(sp.diff(Ay, x) - sp.diff(Ax, y))
assert curl_coeff == 0

# Unit-circle boundary integral: A(gamma(t)) · gamma'(t) dt, t in [0, 2*pi].
gamma = {x: sp.cos(t), y: sp.sin(t)}
dxdt = sp.diff(sp.cos(t), t)
dydt = sp.diff(sp.sin(t), t)
integrand = sp.simplify(Ax.subs(gamma) * dxdt + Ay.subs(gamma) * dydt)
assert integrand == 1
boundary_integral = sp.integrate(integrand, (t, 0, 2 * sp.pi))
assert sp.simplify(boundary_integral - 2 * sp.pi) == 0

# galgebra-oriented bivector residue.
bivector_residue = (boundary_integral * J).simplify()
J_square_galgebra = (J * J).simplify()
assert str(J_square_galgebra) in {"-1", "-1.00000000000000"}

# clifford cross-check: the Euclidean pseudoscalar squares to -1.
from clifford import Cl

layout, blades = Cl(2, 0, firstIdx=0)
c_e0, c_e1 = blades["e0"], blades["e1"]
cJ = c_e0 * c_e1
assert cJ * cJ == -1

# Cross-check a half-angle spinorial monodromy: exp(pi J) = -1 in the Euler lane.
spinor_scalar = sp.cos(sp.pi)
spinor_bivector_coeff = sp.sin(sp.pi)
assert spinor_scalar == -1
assert spinor_bivector_coeff == 0

if __name__ == "__main__":
    print("A =", A)
    print("J =", J)
    print("curl_coeff_off_origin =", curl_coeff)
    print("unit_circle_integrand =", integrand)
    print("boundary_integral =", boundary_integral)
    print("bivector_residue =", bivector_residue)
    print("galgebra_J_square =", J_square_galgebra)
    print("clifford_J_square = -1")
    print("spinor_transport_2pi = -1")
    print("sympy geometric Stokes certificate: ok")

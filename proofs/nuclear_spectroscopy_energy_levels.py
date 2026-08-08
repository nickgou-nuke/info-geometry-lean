#!/usr/bin/env python3
"""
SymPy witness layer for NuclearSpectroscopyEnergyLevels.lean.

This is an external audit/template only: it expands the Goutev--Tonev
rotational-vibrational spectroscopy formulas and checks the normalized
first-generation topological gap.  Lean remains the proof kernel.
"""

import sympy as sp

chi, Z, p = sp.symbols("chi Z p", positive=True)
hbar_omega, A, B = sp.symbols("hbar_omega A B")
decoupling, inertia_factor, sigma = sp.symbols("a I_factor sigma")
n_plus, n_minus = sp.symbols("n_plus n_minus", integer=True, nonnegative=True)
J, K = sp.symbols("J K")
delta = sp.symbols("delta_K_half")

E_top = sp.Abs(chi) / Z * sp.log(p)
E_vib = hbar_omega * (n_plus + n_minus + 1)
E_rot = A * (J * (J + 1) - K**2)
E_cor = sigma * decoupling * inertia_factor * (J + sp.Rational(1, 2)) * delta
E_total = sp.expand(E_top + E_vib + E_rot + E_cor)

E_unified = (
    sp.Abs(chi) / Z * sp.log(p)
    + hbar_omega
    + hbar_omega * (n_plus + n_minus)
    + A * J * (J + 1)
    + (B - A) * K**2
    + E_cor
)

# The Lean theorem states exact agreement with the decomposed rotor when B=0.
identity_B0 = sp.simplify(E_unified.subs(B, 0) - E_total)

normalized_gap = sp.simplify(E_top.subs({chi: 1, Z: 6, p: 2}))

# A concrete half-integer test point, useful for future INRNE mirror-nucleus fits.
example = sp.simplify(
    E_total.subs(
        {
            chi: 1,
            Z: 6,
            p: 2,
            hbar_omega: sp.Rational(3, 2),
            A: sp.Rational(1, 10),
            n_plus: 1,
            n_minus: 0,
            J: sp.Rational(3, 2),
            K: sp.Rational(1, 2),
            sigma: -1,
            decoupling: sp.Rational(2, 5),
            inertia_factor: sp.Rational(1, 10),
            delta: 1,
        }
    )
)

print("E_top     =", E_top)
print("E_vib     =", E_vib)
print("E_rot     =", E_rot)
print("E_cor     =", E_cor)
print("E_total   =", E_total)
print("E_unified(B=0) - E_total =", identity_B0)
print("normalized p=2 top gap   =", normalized_gap)
print("example J=3/2,K=1/2 level =", example)

assert identity_B0 == 0
assert normalized_gap == sp.log(2) / 6
print("SymPy spectroscopy audit passed")

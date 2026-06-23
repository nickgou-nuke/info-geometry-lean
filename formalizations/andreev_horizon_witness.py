#!/usr/bin/env python3
"""Finite Andreev-horizon algebra witness.

This script verifies only the finite BdG/Mobius/DIII matrix algebra used by the
Lean bridge:

  S(e, h) = (-h, e)
  S^2 = -I
  S^T S = I
  trace(S) = 0

and the finite DIII proxy:

  T^2 = -I
  C^2 = I
  S_chiral = T C
  C T = -S_chiral

It does not prove a physical black-hole information theorem.
"""

import sympy as sp


def main() -> None:
    e, h = sp.symbols("e h", real=True)

    state = sp.Matrix([e, h])
    mobius_andreev = sp.Matrix([[0, -1], [1, 0]])
    identity = sp.eye(2)

    reflected = mobius_andreev * state

    assert reflected == sp.Matrix([-h, e])
    assert mobius_andreev * mobius_andreev == -identity
    assert mobius_andreev.T * mobius_andreev == identity
    assert sp.trace(mobius_andreev) == 0

    time_reversal_proxy = mobius_andreev
    particle_hole_proxy = sp.diag(1, -1)
    chiral_proxy = time_reversal_proxy * particle_hole_proxy

    assert time_reversal_proxy * time_reversal_proxy == -identity
    assert particle_hole_proxy * particle_hole_proxy == identity
    assert chiral_proxy == sp.Matrix([[0, 1], [1, 0]])
    assert particle_hole_proxy * time_reversal_proxy == -chiral_proxy
    assert chiral_proxy * chiral_proxy == identity

    condensate_amplitude = e + h
    assert sp.simplify(condensate_amplitude - (e + h)) == 0

    print("Finite BdG/Andreev/DIII horizon witness")
    print("S(e,h) =")
    sp.pprint(reflected)
    print("S^2 =")
    sp.pprint(mobius_andreev * mobius_andreev)
    print("S^T S =")
    sp.pprint(mobius_andreev.T * mobius_andreev)
    print("trace(S) =", sp.trace(mobius_andreev))
    print("DIII chiral proxy T*C =")
    sp.pprint(chiral_proxy)
    print("condensate amplitude marker =", condensate_amplitude)
    print("SUCCESS: finite Andreev/Mobius/DIII particle-hole algebra verified.")


if __name__ == "__main__":
    main()

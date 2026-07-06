#!/usr/bin/env python3
# pyright: reportAttributeAccessIssue=false
"""Exact SymPy verifier for the Hestenes/Krein complex axis packet."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parent
packet = json.loads((ROOT / "cases.json").read_text())

def mat(name: str):
    return sp.Matrix(packet["matrix_convention"][name])

def assert_zero_matrix(M, label: str) -> None:
    if any(sp.simplify(x) != 0 for x in M):
        raise AssertionError(f"{label} failed: {M}")

def main() -> None:
    K = mat("K")
    J = mat("J")
    eps = mat("epsilon")
    I2 = sp.eye(2)
    assert_zero_matrix(K*K + I2, "K^2=-I")
    assert_zero_matrix(J*J - I2, "J^2=I")
    assert_zero_matrix(eps*eps - I2, "eps^2=I")
    assert_zero_matrix(J*eps - K, "J eps = K")
    assert_zero_matrix(eps*J + K, "eps J = -K")
    assert sp.trace(K) == 0

    a,b,c,d = sp.symbols("a b c d")
    rho1 = a*I2 + b*K
    rho2 = c*I2 + d*K
    rho_prod = (a*c - b*d)*I2 + (a*d + b*c)*K
    assert_zero_matrix(sp.expand(rho1*rho2 - rho_prod), "rho multiplicative")

    p,q,r,s = sp.symbols("p q r s")
    A = sp.Matrix([[p,q],[r,s]])
    comm = sp.expand(K*A - A*K)
    expected = sp.Matrix([[-q-r, p-s], [p-s, q+r]])
    assert_zero_matrix(comm - expected, "commutator formula")
    kernel_shape = sp.Matrix([[p,q],[-q,p]])
    assert_zero_matrix(K*kernel_shape - kernel_shape*K, "kernel shape commutes")
    print("SYMPY_HK_COMPLEX_AXIS_OK")

if __name__ == "__main__":
    main()

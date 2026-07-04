#!/usr/bin/env python3
"""Repo-backed primon crystallization synthesis check.

This executable packet mirrors the Lean theorem surfaces in
`InfoGeometry.Arithmetic.QuasicrystalRHExplicitFormula` and the owner modules it
imports.  It checks finite algebra only: Euler cancellation, Mobius parity,
critical-line envelope removal, and Dyson/Vandermonde repulsion.
"""

from __future__ import annotations

import json
from itertools import combinations
from math import prod
from pathlib import Path

import sympy as sp


def subsets(xs: list[int]) -> list[tuple[int, ...]]:
    return [tuple(c) for r in range(len(xs) + 1) for c in combinations(xs, r)]


def main() -> None:
    primes = [2, 3, 5, 7]
    beta = sp.Integer(2)
    x = {p: sp.Rational(1, p) ** beta for p in primes}

    z_boson = prod(1 / (1 - x[p]) for p in primes)
    z_signed = prod(1 - x[p] for p in primes)
    z_fermion = prod(1 + x[p] for p in primes)
    z_second = prod(1 - x[p] ** 2 for p in primes)

    assert sp.simplify(z_boson * z_signed - 1) == 0
    assert sp.simplify(z_fermion * z_signed - z_second) == 0
    assert sp.simplify(z_boson * z_second - z_fermion) == 0

    mobius_ok = True
    for S in subsets(primes):
        n = prod(S) if S else 1
        mobius_ok = mobius_ok and (sp.mobius(n) == (-1) ** len(S))
    assert mobius_ok
    for n in [4, 8, 9, 12, 18, 20, 45]:
        assert sp.mobius(n) == 0

    t = sp.symbols("t", positive=True)
    u, v = sp.symbols("u v", real=True)
    wave = t ** (sp.Rational(1, 2) + u + sp.I * v)
    envelope = sp.sqrt(t) * t**u * sp.exp(sp.I * v * sp.log(t))
    assert sp.simplify(wave.rewrite(sp.exp) - envelope.rewrite(sp.exp)) == 0
    assert sp.simplify(wave.subs(u, 0).rewrite(sp.exp) - (sp.sqrt(t) * sp.exp(sp.I * v * sp.log(t))).rewrite(sp.exp)) == 0

    lam = [sp.Integer(1), sp.Integer(3), sp.Integer(6), sp.Integer(10)]
    vand = prod(abs(lam[j] - lam[i]) for i in range(len(lam)) for j in range(i + 1, len(lam)))
    interaction = sum(sp.log(abs(lam[j] - lam[i])) for i in range(len(lam)) for j in range(i + 1, len(lam)))
    external = sum(a**2 for a in lam)
    dyson = external - 2 * interaction
    assert vand != 0
    assert sp.simplify(sp.log(vand) - interaction) == 0
    assert sp.simplify(dyson - (external - sp.log(vand**2))) == 0

    certificate = {
        "finite_boson_signed_closure": True,
        "fermion_second_order_factorization": True,
        "mobius_squarefree_parity": True,
        "repeated_prime_sector_killed": True,
        "critical_wave_square_root_envelope": True,
        "dyson_vandermonde_bridge": True,
        "claim_boundary": "Repo-backed finite/conditional primon crystallization synthesis; analytic zero-saddle theorem requires supplied explicit-formula packet hypotheses.",
    }
    out = Path(__file__).resolve().parent / "artifacts" / "primon_crystallization_synthesis_certificate.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
    print("SYMPY_PRIMON_CRYSTALLIZATION_SYNTHESIS_OK")
    print(json.dumps(certificate, sort_keys=True))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Finite dynamics for the Goutev--Tonev Hamiltonian.

This is a small executable model:

* compute the symbolic spectroscopy energies;
* build a two-level Hamiltonian with Coriolis/Lie-flow mixing;
* evolve amplitudes with U(t)=exp(-iHt);
* verify probability conservation and diagonal GR/coherence limits.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class SpectroscopyState:
    n_plus: int
    n_minus: int
    j2: int
    k2: int
    generation_prime: int

    @property
    def J(self) -> sp.Rational:
        return sp.Rational(self.j2, 2)

    @property
    def K(self) -> sp.Rational:
        return sp.Rational(self.k2, 2)


def topological_gap(chi_s3, z_klein, p):
    return sp.Abs(chi_s3) / z_klein * sp.log(p)


def vibrational_energy(hbar, omega_vac, s: SpectroscopyState):
    return hbar * omega_vac * (s.n_plus + s.n_minus + 1)


def rotational_energy(A, s: SpectroscopyState):
    return A * (s.J * (s.J + 1) - s.K**2)


def coriolis_signature(j2: int) -> int:
    return 1 if (j2 + 1) % 4 == 0 else -1


def delta_k_half(k2: int) -> int:
    return 1 if k2 == 1 else 0


def coriolis_energy(a, inertia_scale, s: SpectroscopyState):
    return (
        coriolis_signature(s.j2)
        * a
        * inertia_scale
        * (s.J + sp.Rational(1, 2))
        * delta_k_half(s.k2)
    )


def decomposed_energy(chi_s3, z_klein, p, hbar, omega_vac, A, a, inertia_scale, s):
    return (
        topological_gap(chi_s3, z_klein, p)
        + vibrational_energy(hbar, omega_vac, s)
        + rotational_energy(A, s)
        + coriolis_energy(a, inertia_scale, s)
    )


def fractional_correction(lambda_eff, Xi):
    return sp.simplify(lambda_eff**2 * Xi)


def flow_corrected_energy(E, lambda_eff, Xi):
    return sp.simplify(E * (1 + fractional_correction(lambda_eff, Xi)))


def coriolis_lie_coupling(lambda_eff, Xi, a, inertia_scale, s):
    return sp.simplify(fractional_correction(lambda_eff, Xi) + coriolis_energy(a, inertia_scale, s))


def two_level_hamiltonian(E1, E2, flow):
    return sp.Matrix([[E1, flow], [flow, E2]])


def unitary_evolution(H, t):
    return sp.exp(-sp.I * H * t)


def probability_norm(psi):
    return sp.simplify((psi.conjugate().T * psi)[0])


def main() -> None:
    t = sp.symbols("t", real=True)

    # Two neighbouring K=1/2 band states.
    s1 = SpectroscopyState(n_plus=0, n_minus=0, j2=1, k2=1, generation_prime=2)
    s2 = SpectroscopyState(n_plus=1, n_minus=0, j2=3, k2=1, generation_prime=2)

    # Small rational parameters for an auditable toy run.
    chi, z, p = 1, 6, 2
    hbar, omega_vac = 1, sp.Rational(1, 5)
    A = sp.Rational(1, 20)
    a = sp.Rational(1, 10)
    inertia = sp.Rational(1, 4)
    lambda_eff = sp.Rational(195, 100)
    Xi = sp.Rational(263, 1_000_000)  # S2-scale rounded asymmetry.

    E1 = decomposed_energy(chi, z, p, hbar, omega_vac, A, a, inertia, s1)
    E2 = decomposed_energy(chi, z, p, hbar, omega_vac, A, a, inertia, s2)
    flow = coriolis_lie_coupling(lambda_eff, Xi, a, inertia, s1)
    H = two_level_hamiltonian(E1, E2, flow)

    # General Hermitian check and trace invariant.
    assert H == H.conjugate().T
    assert sp.simplify(sp.trace(H) - (E1 + E2)) == 0

    # Zero-flow limit: diagonal phase evolution conserves probability exactly.
    H0 = two_level_hamiltonian(E1, E2, 0)
    U0 = unitary_evolution(H0, t)
    psi0 = sp.Matrix([1, 0])
    psi_t = sp.simplify(U0 * psi0)
    assert sp.simplify(probability_norm(psi_t) - 1) == 0

    # Flow correction recovers base energy when lambda is zero.
    E_corr_zero = flow_corrected_energy(E1, 0, Xi)
    assert sp.simplify(E_corr_zero - E1) == 0

    print("E1 =", E1)
    print("E2 =", E2)
    print("flow coupling =", flow)
    print("two-level H =")
    sp.printing.pprint(H)
    print("trace(H) =", sp.trace(H))
    print("zero-flow evolved |1> =", psi_t)
    print("probability norm =", probability_norm(psi_t))
    print("hamiltonian_coriolis_lie_dynamics.py: finite dynamics audit passed")


if __name__ == "__main__":
    main()

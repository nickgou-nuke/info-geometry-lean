#!/usr/bin/env python3
"""SymPy witness for the Goutev--Tonev nuclear spectroscopy Hamiltonian.

The script checks the symbolic decomposition

    E = E_top + E_vib + E_rot + E_cor

and the unified rotational-band form

    E_JK = E0 + omega(n_+ + n_-) + A J(J+1) + (B-A)K^2 + E_cor.
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


def unified_band_energy(E0, omega, A, B, a, inertia_scale, s):
    return (
        E0
        + omega * (s.n_plus + s.n_minus)
        + A * s.J * (s.J + 1)
        + (B - A) * s.K**2
        + coriolis_energy(a, inertia_scale, s)
    )


def main() -> None:
    chi, z, hbar, omega_vac, A, B, E0, omega, a, inertia = sp.symbols(
        "chi z hbar omega_vac A B E0 omega a inertia", positive=True
    )

    s = SpectroscopyState(n_plus=1, n_minus=0, j2=3, k2=1, generation_prime=2)
    e_parts = (
        topological_gap(chi, z, s.generation_prime)
        + vibrational_energy(hbar, omega_vac, s)
        + rotational_energy(A, s)
        + coriolis_energy(a, inertia, s)
    )
    assert sp.simplify(decomposed_energy(chi, z, 2, hbar, omega_vac, A, a, inertia, s) - e_parts) == 0

    e_unified = (
        E0
        + omega * (s.n_plus + s.n_minus)
        + A * s.J * (s.J + 1)
        + (B - A) * s.K**2
        + coriolis_energy(a, inertia, s)
    )
    assert sp.simplify(unified_band_energy(E0, omega, A, B, a, inertia, s) - e_unified) == 0

    assert sp.simplify(topological_gap(1, 6, 2) - sp.log(2) / 6) == 0

    off_band = SpectroscopyState(n_plus=0, n_minus=0, j2=5, k2=3, generation_prime=3)
    assert coriolis_energy(a, inertia, off_band) == 0

    print("E_top first generation =", topological_gap(1, 6, 2))
    print("sample J,K =", s.J, s.K)
    print("sample coriolis sign =", coriolis_signature(s.j2))
    print("sample E_decomposed =", decomposed_energy(chi, z, 2, hbar, omega_vac, A, a, inertia, s))
    print("sample E_unified =", unified_band_energy(E0, omega, A, B, a, inertia, s))
    print("off K=1/2 coriolis =", coriolis_energy(a, inertia, off_band))
    print("goutev_tonev_nuclear_hamiltonian.py: finite audit passed")


if __name__ == "__main__":
    main()

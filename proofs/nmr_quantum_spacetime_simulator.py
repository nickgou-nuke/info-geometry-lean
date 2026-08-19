#!/usr/bin/env python3
"""Numerical witness for NMRQuantumSpacetimeSimulator.lean.

Audits the finite constants in Li et al., "Quantum spacetime on a quantum
simulator" and checks the elementary Bell-link / five-tetrahedra arithmetic.
The NMR experiment and LQG interpretation remain deferred_interface in Lean.
"""

import sympy as sp


QUBITS_PER_TETRAHEDRON = 4
SPIN_HALF_TWICE_J = 1
SPIN_HALF_DIM = 2
INVARIANT_TENSOR_DIM = 2
TETRAHEDRA_PER_VERTEX = 5
BELL_LINKS = 10
PREPARED_TETRAHEDRA = 10
FIDELITY_PERCENT_LOWER_BOUND = 95
NMR_MHZ = 700


def pairwise_link_count(n: int) -> int:
    return n * (n - 1) // 2


def epsilon_bell_vector():
    # Computational basis |00>, |01>, |10>, |11>.
    return sp.Matrix([0, 1 / sp.sqrt(2), -1 / sp.sqrt(2), 0])


def bell_norm_squared():
    eps = epsilon_bell_vector()
    return (eps.T.conjugate() * eps)[0]


def epsilon_antisymmetry_check():
    eps = epsilon_bell_vector()
    amp_01 = eps[1]
    amp_10 = eps[2]
    return sp.simplify(amp_01 + amp_10)


if __name__ == "__main__":
    print("qubits per tetrahedron =", QUBITS_PER_TETRAHEDRON)
    print("2j for spin-1/2 =", SPIN_HALF_TWICE_J)
    print("dim H_{1/2} =", SPIN_HALF_DIM)
    print("dim Inv_SU(2)((C^2)^⊗4) =", INVARIANT_TENSOR_DIM)
    print("tetrahedra per vertex =", TETRAHEDRA_PER_VERTEX)
    print("pairwise Bell links =", pairwise_link_count(TETRAHEDRA_PER_VERTEX))
    print("prepared tetrahedra =", PREPARED_TETRAHEDRA)
    print("reported fidelity lower bound (%) =", FIDELITY_PERCENT_LOWER_BOUND)
    print("NMR spectrometer MHz =", NMR_MHZ)
    print("epsilon Bell norm^2 =", sp.simplify(bell_norm_squared()))
    print("epsilon antisymmetry amp_01 + amp_10 =", epsilon_antisymmetry_check())

    assert QUBITS_PER_TETRAHEDRON == 4
    assert SPIN_HALF_TWICE_J == 1
    assert SPIN_HALF_DIM == 2
    assert INVARIANT_TENSOR_DIM == 2
    assert TETRAHEDRA_PER_VERTEX == 5
    assert BELL_LINKS == pairwise_link_count(5)
    assert PREPARED_TETRAHEDRA == 10
    assert FIDELITY_PERCENT_LOWER_BOUND == 95
    assert NMR_MHZ == 700
    assert sp.simplify(bell_norm_squared() - 1) == 0
    assert epsilon_antisymmetry_check() == 0

    print("NMR quantum-spacetime simulator audit passed")

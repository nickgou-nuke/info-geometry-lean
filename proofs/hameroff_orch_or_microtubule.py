#!/usr/bin/env python3
"""SymPy audit for HameroffOrchORMicrotubule.lean.

This checks the explicit arithmetic extracted from Hameroff (1998):
E = h/T scaling as tubulin-count examples, microtubule lattice constants,
Fibonacci helical periods, the quantum-computing figure of merit, and a
six-neighbour dipole-coupling skeleton.  It does not validate Orch OR as
biology or quantum gravity.
"""

import sympy as sp


MICROTUBULE_DIAMETER_NM = 25
PROTOFILAMENT_COLUMNS = 13
LATTICE_NEIGHBOURS = 6
AUTOMATON_STEP_NS = 8
BJERRUM_LENGTH_NM = sp.Rational(7, 10)

TUBULIN_MS_CONSTANT = 500_000_000_000
TUBULINS_PER_NEURON = 10_000_000
COHERENT_FRACTION = sp.Rational(1, 10)
COHERENT_TUBULINS_PER_NEURON = int(TUBULINS_PER_NEURON * COHERENT_FRACTION)


def objective_reduction_energy(h, T):
    return h / T


def predicted_tubulins(T_ms: int) -> int:
    return TUBULIN_MS_CONSTANT // T_ms


def neurons_required(T_ms: int) -> int:
    return predicted_tubulins(T_ms) // COHERENT_TUBULINS_PER_NEURON


def figure_of_merit(t_elem, t_decohere):
    return sp.simplify(t_decohere / t_elem)


def six_neighbour_coupling(prefactor, weights, inverse_distances):
    assert len(weights) == LATTICE_NEIGHBOURS
    assert len(inverse_distances) == LATTICE_NEIGHBOURS
    return sp.simplify(prefactor * sum(w * d for w, d in zip(weights, inverse_distances)))


if __name__ == "__main__":
    print("microtubule diameter (nm) =", MICROTUBULE_DIAMETER_NM)
    print("protofilament columns =", PROTOFILAMENT_COLUMNS)
    print("local lattice neighbours =", LATTICE_NEIGHBOURS)
    print("automaton step (ns) =", AUTOMATON_STEP_NS)
    print("Bjerrum length (nm) =", BJERRUM_LENGTH_NM)

    for T_ms in (25, 100, 500):
        print(f"predicted tubulins at {T_ms} ms =", predicted_tubulins(T_ms))
        print(f"neurons required at {T_ms} ms =", neurons_required(T_ms))

    periods = [3, 5, 8, 13]
    print("helical Fibonacci periods =", periods)
    print("figure of merit =", figure_of_merit(sp.Rational(1, 10**9), sp.Rational(1, 10)))

    weights = sp.symbols("w0:6")
    inv_distances = sp.symbols("r0:6")
    zero_prefactor_coupling = six_neighbour_coupling(0, weights, inv_distances)
    print("zero-prefactor six-neighbour coupling =", zero_prefactor_coupling)

    h, T = sp.symbols("h T", nonzero=True)
    assert objective_reduction_energy(h, T) == h / T
    assert MICROTUBULE_DIAMETER_NM == 25
    assert PROTOFILAMENT_COLUMNS == 13
    assert LATTICE_NEIGHBOURS == 6
    assert AUTOMATON_STEP_NS == 8
    assert BJERRUM_LENGTH_NM == sp.Rational(7, 10)
    assert predicted_tubulins(25) == 20_000_000_000
    assert predicted_tubulins(100) == 5_000_000_000
    assert predicted_tubulins(500) == 1_000_000_000
    assert COHERENT_TUBULINS_PER_NEURON == 1_000_000
    assert neurons_required(25) == 20_000
    assert neurons_required(100) == 5_000
    assert neurons_required(500) == 1_000
    assert periods[0] + periods[1] == periods[2]
    assert periods[1] + periods[2] == periods[3]
    assert figure_of_merit(sp.Rational(1, 10**9), sp.Rational(1, 10)) == 100_000_000
    assert zero_prefactor_coupling == 0

    print("Hameroff Orch OR microtubule arithmetic audit passed")

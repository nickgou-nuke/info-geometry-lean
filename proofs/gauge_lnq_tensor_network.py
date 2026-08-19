#!/usr/bin/env python3
"""Finite U(1) gauge ln(Q) tensor-network toy.

External numerical witness only.  This promotes the previous ln(Q) node-potential
Boltzmann model to a finite lattice-gauge/tensor-network deferred_interface:

* node matter amplitudes psi_i(s_i) built from positive Q_i(s_i),
* U(1) edge links U_ij,
* local gauge transforms psi_i -> g_i psi_i, U_ij -> g_i U_ij g_j^*,
* gauge-invariant edge energy Re(psi_i^* U_ij psi_j),
* gauge-invariant triangular Wilson loops U_ij U_jk U_ki.

Run:
    cd /home/goutev/auto
    external/repos/trainsum/.venv/bin/python proofs/gauge_lnq_tensor_network.py
"""

from __future__ import annotations

import json
import math
import pathlib
import sys

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
TRAINSUM_REPO = ROOT / "external" / "repos" / "trainsum"
if str(TRAINSUM_REPO) not in sys.path:
    sys.path.insert(0, str(TRAINSUM_REPO))

from trainsum import TrainSum

N = 6
BETA = 1.1
J = 0.04
KAPPA = 0.025


def edges(n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def triangles(n: int) -> list[tuple[int, int, int]]:
    return [(i, j, k) for i in range(n) for j in range(i + 1, n) for k in range(j + 1, n)]


def q_table(n: int) -> np.ndarray:
    q = np.zeros((n, 2), dtype=float)
    for i in range(n):
        base = 1.25 + 0.06 * i
        tilt = 0.08 + 0.01 * (i % 2)
        q[i, 0] = base - tilt
        q[i, 1] = base + tilt
    return q


def link(i: int, j: int) -> complex:
    # Deterministic antisymmetric U(1) phase on i<j.
    angle = 0.17 * (i + 1) - 0.11 * (j + 1) + 0.03 * (i + 1) * (j + 1)
    return complex(np.exp(1j * angle))


def link_lookup(U: dict[tuple[int, int], complex], i: int, j: int) -> complex:
    if i < j:
        return U[(i, j)]
    return np.conjugate(U[(j, i)])


def all_states(n: int) -> np.ndarray:
    dim = 2**n
    return ((np.arange(dim)[:, None] >> np.arange(n - 1, -1, -1)) & 1).astype(int)


def energy(states: np.ndarray, psi: np.ndarray, U: dict[tuple[int, int], complex]) -> np.ndarray:
    q = np.abs(psi) ** 2
    logq = np.log(q)
    e = np.zeros(states.shape[0], dtype=float)
    for idx, bits in enumerate(states):
        node = -sum(logq[i, bits[i]] for i in range(N))
        edge_e = 0.0
        for i, j in edges(N):
            edge_e += np.real(np.conjugate(psi[i, bits[i]]) * link_lookup(U, i, j) * psi[j, bits[j]])
        wilson = 0.0
        for i, j, k in triangles(N):
            wilson += np.real(link_lookup(U, i, j) * link_lookup(U, j, k) * link_lookup(U, k, i))
        e[idx] = node - J * edge_e - KAPPA * wilson
    return e


def gauge_transform(psi: np.ndarray, U: dict[tuple[int, int], complex]) -> tuple[np.ndarray, dict[tuple[int, int], complex]]:
    alpha = np.array([0.13 * (i + 1) ** 2 - 0.07 * i for i in range(N)])
    g = np.exp(1j * alpha)
    psi2 = psi * g[:, None]
    U2 = {}
    for i, j in edges(N):
        U2[(i, j)] = g[i] * U[(i, j)] * np.conjugate(g[j])
    return psi2, U2


def boltzmann(e: np.ndarray) -> np.ndarray:
    x = -BETA * e
    x -= x.max()
    w = np.exp(x)
    return w / w.sum()


def main() -> None:
    q = q_table(N)
    psi = np.sqrt(q).astype(complex)
    U = {(i, j): link(i, j) for i, j in edges(N)}
    psi_g, U_g = gauge_transform(psi, U)
    states = all_states(N)
    e0 = energy(states, psi, U)
    e1 = energy(states, psi_g, U_g)
    p = boltzmann(e0)

    ts = TrainSum(np)
    shape = ts.trainshape(2**N, mode="block")
    with ts.exact():
        train = ts.tensortrain(shape, p)
    recon = train.to_tensor()

    result = {
        "nodes": N,
        "state_count": 2**N,
        "edge_count": len(edges(N)),
        "triangle_count": len(triangles(N)),
        "q_min": float(q.min()),
        "gauge_energy_difference_norm": float(np.linalg.norm(e0 - e1)),
        "probability_sum": float(p.sum()),
        "qtt_reconstruction_error": float(np.linalg.norm(recon - p)),
        "first_wilson_loop_real": float(np.real(link_lookup(U, 0, 1) * link_lookup(U, 1, 2) * link_lookup(U, 2, 0))),
        "qtt_core_shapes": [tuple(int(x) for x in core.shape) for core in train.cores],
    }
    print(json.dumps(result, indent=2))
    assert result["nodes"] == 6
    assert result["edge_count"] == 15
    assert result["triangle_count"] == 20
    assert result["q_min"] > 0
    assert result["gauge_energy_difference_norm"] < 1e-12
    assert abs(result["probability_sum"] - 1.0) < 1e-12
    assert result["qtt_reconstruction_error"] < 1e-12
    print("Gauge lnQ tensor-network toy audit passed")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Toy Penrose/chiral many-body nuclear tensor-train audit.

This is an external numerical witness, not a theorem prover.  It builds a small
finite spin-1/2 Hamiltonian whose couplings are arranged by a Fibonacci/Penrose-
inspired chord graph, checks a chiral/parity selection rule in dense form, then
stores the ground-state vector as a quantics tensor train using `trainsum`.

Run with the trainsum Python 3.14 environment, e.g.

    cd /home/goutev/auto
    external/repos/trainsum/.venv/bin/python proofs/penrose_chiral_nuclear_trainsum.py
"""

from __future__ import annotations

import json
import math
import pathlib
import sys
from dataclasses import dataclass

import numpy as np

# Allow running from /home/goutev/auto while using the locally cloned trainsum.
ROOT = pathlib.Path(__file__).resolve().parents[1]
TRAINSUM_REPO = ROOT / "external" / "repos" / "trainsum"
if str(TRAINSUM_REPO) not in sys.path:
    sys.path.insert(0, str(TRAINSUM_REPO))

try:
    from trainsum import TrainSum
except Exception as exc:  # pragma: no cover - diagnostic for wrong interpreter/env
    raise SystemExit(
        "Could not import trainsum. Run with "
        f"{TRAINSUM_REPO}/.venv/bin/python or install trainsum first.\n{exc}"
    ) from exc


@dataclass(frozen=True)
class ToyParams:
    nsites: int = 8
    jxy: float = 0.18
    delta: float = 0.07
    chirality: float = 0.025
    onsite_scale: float = 0.11


def fibonacci_word(n: int) -> list[int]:
    """First n bits of a Fibonacci/Sturmian word using the golden slope."""
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    alpha = 1.0 / phi
    return [math.floor((k + 1) * alpha) - math.floor(k * alpha) for k in range(n)]


def penrose_chord_edges(n: int) -> list[tuple[int, int]]:
    """Small deterministic Penrose-inspired graph: cycle + Fibonacci chords."""
    edges: set[tuple[int, int]] = set()
    for i in range(n):
        a, b = i, (i + 1) % n
        edges.add(tuple(sorted((a, b))))
    word = fibonacci_word(n)
    for i, bit in enumerate(word):
        step = 2 if bit == 1 else 3
        a, b = i, (i + step) % n
        if a != b:
            edges.add(tuple(sorted((a, b))))
    return sorted(edges)


def chiral_triangles(edges: list[tuple[int, int]], n: int) -> list[tuple[int, int, int]]:
    edge_set = set(edges)
    tris: list[tuple[int, int, int]] = []
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                if ((i, j) in edge_set) and ((j, k) in edge_set) and ((i, k) in edge_set):
                    tris.append((i, j, k))
    return tris


I2 = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)


def local_op(n: int, ops: dict[int, np.ndarray]) -> np.ndarray:
    acc = np.array([[1]], dtype=complex)
    for site in range(n):
        acc = np.kron(acc, ops.get(site, I2))
    return acc


def build_hamiltonian(params: ToyParams) -> tuple[np.ndarray, dict[str, object]]:
    n = params.nsites
    edges = penrose_chord_edges(n)
    triangles = chiral_triangles(edges, n)
    word = fibonacci_word(n)
    dim = 2**n
    H = np.zeros((dim, dim), dtype=complex)

    # Nuclear/spectroscopic toy onsite splittings: Fibonacci modulation.
    for i, bit in enumerate(word):
        eps = params.onsite_scale * (1.0 + 0.5 * bit)
        H += eps * local_op(n, {i: Z})

    # Pair couplings preserve spin parity: XX + YY + Delta ZZ.
    for i, j in edges:
        H += params.jxy * (local_op(n, {i: X, j: X}) + local_op(n, {i: Y, j: Y}))
        H += params.delta * local_op(n, {i: Z, j: Z})

    # Oriented chiral plaquette toy term, also parity preserving.
    for i, j, k in triangles:
        H += params.chirality * (
            local_op(n, {i: Z, j: X, k: Y}) - local_op(n, {i: Z, j: Y, k: X})
        )

    meta = {"word": word, "edges": edges, "triangles": triangles}
    return H, meta


def parity_operator(n: int) -> np.ndarray:
    return local_op(n, {i: Z for i in range(n)})


def parity_offdiag_norm(operator: np.ndarray, parity: np.ndarray) -> float:
    plus = (np.eye(operator.shape[0], dtype=complex) + parity) / 2.0
    minus = (np.eye(operator.shape[0], dtype=complex) - parity) / 2.0
    return float(np.linalg.norm(plus @ operator @ minus) + np.linalg.norm(minus @ operator @ plus))


def main() -> None:
    params = ToyParams()
    H, meta = build_hamiltonian(params)
    n = params.nsites
    P = parity_operator(n)

    herm_err = float(np.linalg.norm(H - H.conj().T))
    comm_err = float(np.linalg.norm(H @ P - P @ H))
    offdiag = parity_offdiag_norm(H, P)
    evals, evecs = np.linalg.eigh(H)
    ground = evecs[:, 0]

    # Quantics tensor train exact storage/reconstruction audit.
    ts = TrainSum(np)
    shape = ts.trainshape(2**n, mode="block")
    with ts.exact():
        train = ts.tensortrain(shape, ground)
    recon = train.to_tensor()
    recon_err = float(np.linalg.norm(recon - ground))
    core_shapes = [tuple(int(x) for x in core.shape) for core in train.cores]

    result = {
        "nsites": n,
        "hilbert_dim": int(2**n),
        "fibonacci_word": meta["word"],
        "edge_count": len(meta["edges"]),
        "edges": meta["edges"],
        "triangle_count": len(meta["triangles"]),
        "triangles": meta["triangles"],
        "hermitian_error": herm_err,
        "parity_commutator_norm": comm_err,
        "parity_offdiag_norm": offdiag,
        "ground_energy": float(evals[0].real),
        "first_gap": float((evals[1] - evals[0]).real),
        "qtt_core_shapes": core_shapes,
        "qtt_reconstruction_error": recon_err,
    }

    print(json.dumps(result, indent=2))

    assert herm_err < 1e-10
    assert comm_err < 1e-10
    assert offdiag < 1e-10
    assert recon_err < 1e-10
    assert len(meta["edges"]) == 16
    assert len(meta["triangles"]) == 8
    print("Penrose/chiral nuclear trainsum toy audit passed")


if __name__ == "__main__":
    main()

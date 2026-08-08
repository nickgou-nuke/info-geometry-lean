#!/usr/bin/env python3
"""Frozen O(5,5) / Pin(5,5) manifold-flow toy.

This is the finite numerical analogue of the CUAI equivariant-manifold-flow
idea: build a symmetry-compatible vector field, freeze protected coordinates,
and learn/evolve only the active parameters.

We use the split metric

    eta = diag(+1,+1,+1,+1,+1,-1,-1,-1,-1,-1)

and project an arbitrary trainable matrix B to the Lie algebra o(5,5):

    A = 1/2 * (B - eta B.T eta)

so that A.T eta + eta A = 0.  The flow exp(tA) preserves x.T eta x.
Rows/columns belonging to frozen coordinates are zeroed before projection, so
those coordinates remain fixed.
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
from scipy.linalg import expm

from nuclear_chart_square_calibration import (
    demo_levels,
    fit_square_constants,
    read_levels,
    square_vertex_hamiltonian,
)


def eta55() -> np.ndarray:
    return np.diag([1.0] * 5 + [-1.0] * 5)


def project_o55(matrix: np.ndarray, eta: np.ndarray) -> np.ndarray:
    return 0.5 * (matrix - eta @ matrix.T @ eta)


def freeze_matrix(matrix: np.ndarray, frozen: list[int]) -> np.ndarray:
    frozen_matrix = np.array(matrix, dtype=float, copy=True)
    for idx in frozen:
        frozen_matrix[idx, :] = 0.0
        frozen_matrix[:, idx] = 0.0
    return frozen_matrix


def o55_residual(generator: np.ndarray, eta: np.ndarray) -> float:
    return float(np.linalg.norm(generator.T @ eta + eta @ generator))


def quadratic_form(x: np.ndarray, eta: np.ndarray) -> float:
    return float(x.T @ eta @ x)


def square_features(data: Path | None) -> np.ndarray:
    levels = read_levels(data) if data else demo_levels()
    params, _ = fit_square_constants(levels)
    _, hamiltonian, eigenvalues = square_vertex_hamiltonian(params, levels)
    features = np.zeros(10)
    features[:4] = np.diag(hamiltonian)
    features[4] = params["zn_coupling"]
    features[5:9] = eigenvalues
    features[9] = params["omega"]
    scale = max(np.linalg.norm(features), 1.0)
    return features / scale


def trainable_seed_from_features(features: np.ndarray) -> np.ndarray:
    # Deterministic finite "learned" generator seed from the calibrated square
    # features.  This is not fitting; it is an auditable embedding map.
    b = np.zeros((10, 10))
    active = list(range(4, 10))
    for row_pos, i in enumerate(active):
        for col_pos, j in enumerate(active):
            if i != j:
                b[i, j] = features[(row_pos + col_pos) % len(features)]
    return b


def run_flow(data: Path | None, time: float) -> dict[str, object]:
    eta = eta55()
    frozen = [0, 1, 2, 3]
    features = square_features(data)
    seed = trainable_seed_from_features(features)
    generator = project_o55(freeze_matrix(seed, frozen), eta)
    flow = expm(time * generator)
    x0 = features
    x1 = flow @ x0

    return {
        "features": features,
        "generator": generator,
        "flow": flow,
        "x0": x0,
        "x1": x1,
        "o55_residual": o55_residual(generator, eta),
        "flow_residual": float(np.linalg.norm(flow.T @ eta @ flow - eta)),
        "quadratic_before": quadratic_form(x0, eta),
        "quadratic_after": quadratic_form(x1, eta),
        "frozen_displacement": float(np.linalg.norm(x1[frozen] - x0[frozen])),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, help="CSV file with adopted square levels")
    parser.add_argument("--time", type=float, default=0.7)
    args = parser.parse_args()

    result = run_flow(args.data, args.time)

    print("feature vector =", np.array2string(result["features"], precision=6, suppress_small=True))
    print("o(5,5) generator residual =", f"{result['o55_residual']:.3e}")
    print("O(5,5) flow residual =", f"{result['flow_residual']:.3e}")
    print("quadratic before =", f"{result['quadratic_before']:.12f}")
    print("quadratic after  =", f"{result['quadratic_after']:.12f}")
    print("frozen coordinate displacement =", f"{result['frozen_displacement']:.3e}")
    print("evolved active coordinates =", np.array2string(result["x1"][4:], precision=6, suppress_small=True))

    assert result["o55_residual"] < 1e-12
    assert result["flow_residual"] < 1e-12
    assert abs(result["quadratic_after"] - result["quadratic_before"]) < 1e-12
    assert result["frozen_displacement"] < 1e-12
    print("frozen_pin55_manifold_flow.py: frozen O(5,5) flow audit passed")


if __name__ == "__main__":
    main()

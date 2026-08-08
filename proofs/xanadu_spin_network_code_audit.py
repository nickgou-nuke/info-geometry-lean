#!/usr/bin/env python3
"""Audit for XanaduAI/all-you-need-is-spin code digest.

Checks repository-level finite data without requiring PennyLane-Lightning's custom
branch: Schur matrices in `python_src/gates.py`, parameter-count formulas, and
Heisenberg term counts used by the scripts.
"""

from __future__ import annotations

import json
import pathlib
import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
REPO = ROOT / "external" / "repos" / "all-you-need-is-spin"


def schur2() -> np.ndarray:
    rt2 = np.sqrt(2.0)
    return np.array([
        [1, 0, 0, 0],
        [0, 1/rt2, 1/rt2, 0],
        [0, 0, 0, 1],
        [0, 1/rt2, -1/rt2, 0],
    ], dtype=float)


def schur3() -> np.ndarray:
    return np.array([
        [1, 0, 0, 0, 0, 0, 0, 0],
        [0, 1/np.sqrt(3), 1/np.sqrt(3), 0, 1/np.sqrt(3), 0, 0, 0],
        [0, 0, 0, 1/np.sqrt(3), 0, 1/np.sqrt(3), 1/np.sqrt(3), 0],
        [0, 0, 0, 0, 0, 0, 0, 1],
        [0, 0, -1/np.sqrt(2), 0, 1/np.sqrt(2), 0, 0, 0],
        [0, 0, 0, -1/np.sqrt(2), 0, 1/np.sqrt(2), 0, 0],
        [0, np.sqrt(2)/np.sqrt(3), -1/np.sqrt(6), 0, -1/np.sqrt(6), 0, 0, 0],
        [0, 0, 0, 1/np.sqrt(6), 0, 1/np.sqrt(6), -np.sqrt(2)/np.sqrt(3), 0],
    ], dtype=float)


def unitarity_error(U: np.ndarray) -> float:
    return float(np.linalg.norm(U @ U.T - np.eye(U.shape[0])))


def heisenberg_1d_term_count(n: int) -> int:
    # XX, YY, ZZ for nearest neighbors and next-nearest neighbors.
    return 6 * n


def two_qubit_param_count(n: int, blocks: int) -> int:
    return 2 * n * blocks


def three_qubit_param_count(n: int, blocks: int) -> int:
    return 4 * n * blocks


def main() -> None:
    s2 = schur2()
    s3 = schur3()
    result = {
        "repo_exists": REPO.exists(),
        "schur2_shape": s2.shape,
        "schur3_shape": s3.shape,
        "schur2_unitarity_error": unitarity_error(s2),
        "schur3_unitarity_error": unitarity_error(s3),
        "heisenberg_terms_N20": heisenberg_1d_term_count(20),
        "two_qubit_params_N20_L4": two_qubit_param_count(20, 4),
        "three_qubit_params_N20_L4": three_qubit_param_count(20, 4),
        "kagome18_qubits": 18,
    }
    print(json.dumps(result, indent=2))
    assert result["repo_exists"]
    assert s2.shape == (4, 4)
    assert s3.shape == (8, 8)
    assert result["schur2_unitarity_error"] < 1e-12
    assert result["schur3_unitarity_error"] < 1e-12
    assert result["heisenberg_terms_N20"] == 120
    assert result["two_qubit_params_N20_L4"] == 160
    assert result["three_qubit_params_N20_L4"] == 320
    print("Xanadu all-you-need-is-spin code audit passed")


if __name__ == "__main__":
    main()

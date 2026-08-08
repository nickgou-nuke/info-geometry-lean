#!/usr/bin/env python3
"""All-connected Boltzmann tensor-net toy with ln(Q) node potentials and flow.

External numerical witness only.  The model is a finite complete-graph Ising-like
Boltzmann distribution

    E_t(s) = - Σ_i θ_i(t) log Q_i(s_i) - J Σ_{i<j} s_i s_j,
    p_t(s) = exp(-β E_t(s)) / Z_t,

where each node has a positive two-state `Q_i`, so `log Q_i` is well-defined.
The node parameters θ evolve by a simple dissipative/feedback vector field.  The
final probability tensor is stored exactly as a quantics tensor train using the
locally installed `trainsum` package.

Run:
    cd /home/goutev/auto
    external/repos/trainsum/.venv/bin/python proofs/boltzmann_lnq_tensor_flow.py
"""

from __future__ import annotations

import json
import math
import pathlib
import sys
from dataclasses import dataclass

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
TRAINSUM_REPO = ROOT / "external" / "repos" / "trainsum"
if str(TRAINSUM_REPO) not in sys.path:
    sys.path.insert(0, str(TRAINSUM_REPO))

try:
    from trainsum import TrainSum
except Exception as exc:  # pragma: no cover
    raise SystemExit(
        "Could not import trainsum. Run with "
        f"{TRAINSUM_REPO}/.venv/bin/python or install trainsum first.\n{exc}"
    ) from exc


@dataclass(frozen=True)
class FlowParams:
    nsites: int = 6
    beta: float = 1.25
    coupling: float = 0.035
    dt: float = 0.08
    steps: int = 12
    damping: float = 0.45
    feedback: float = 0.25


def complete_edges(n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def spin_table(n: int) -> np.ndarray:
    """All ±1 spin states, shape `(2^n,n)`."""
    dim = 2**n
    bits = ((np.arange(dim)[:, None] >> np.arange(n - 1, -1, -1)) & 1).astype(float)
    return 2.0 * bits - 1.0


def q_values(n: int) -> np.ndarray:
    """Positive node Q-values, shape `(n,2)` for spin -1,+1."""
    q = np.zeros((n, 2), dtype=float)
    for i in range(n):
        base = 1.35 + 0.07 * i
        tilt = 0.11 + 0.01 * (i % 3)
        q[i, 0] = base - tilt  # spin -1
        q[i, 1] = base + tilt  # spin +1
    assert float(q.min()) > 0.0
    return q


def logq_features(spins: np.ndarray, q: np.ndarray) -> np.ndarray:
    idx = (spins > 0).astype(int)
    out = np.zeros_like(spins, dtype=float)
    for i in range(spins.shape[1]):
        out[:, i] = np.log(q[i, idx[:, i]])
    return out


def energy(spins: np.ndarray, logq: np.ndarray, theta: np.ndarray, edges: list[tuple[int, int]], coupling: float) -> np.ndarray:
    node = -logq @ theta
    pair = np.zeros(spins.shape[0], dtype=float)
    for i, j in edges:
        pair += spins[:, i] * spins[:, j]
    return node - coupling * pair


def boltzmann(energies: np.ndarray, beta: float) -> tuple[np.ndarray, float]:
    x = -beta * energies
    shift = float(x.max())
    w = np.exp(x - shift)
    z_scaled = float(w.sum())
    p = w / z_scaled
    log_z = shift + math.log(z_scaled)
    return p, log_z


def vector_field(theta: np.ndarray, expected_logq: np.ndarray, target: np.ndarray, params: FlowParams) -> np.ndarray:
    # A deliberately simple dissipative feedback law.  It is not asserted to be
    # physical; it just supplies a finite flow socket over ln(Q)-observables.
    return -params.damping * theta + params.feedback * (target - expected_logq)


def run_flow(params: FlowParams) -> dict[str, object]:
    n = params.nsites
    edges = complete_edges(n)
    spins = spin_table(n)
    q = q_values(n)
    logq = logq_features(spins, q)
    target = np.linspace(float(logq.mean()) - 0.04, float(logq.mean()) + 0.04, n)
    theta = np.linspace(-0.18, 0.22, n)

    history: list[dict[str, object]] = []
    for step in range(params.steps + 1):
        e = energy(spins, logq, theta, edges, params.coupling)
        p, log_z = boltzmann(e, params.beta)
        expected_logq = p @ logq
        entropy = float(-np.sum(p * np.log(p + 1e-300)))
        free_energy = float(-log_z / params.beta)
        history.append(
            {
                "step": step,
                "theta_norm": float(np.linalg.norm(theta)),
                "prob_sum": float(p.sum()),
                "entropy": entropy,
                "free_energy": free_energy,
                "expected_logq_mean": float(expected_logq.mean()),
            }
        )
        if step < params.steps:
            theta = theta + params.dt * vector_field(theta, expected_logq, target, params)

    # Quantics tensor-train exact encoding of final probability vector.
    ts = TrainSum(np)
    shape = ts.trainshape(2**n, mode="block")
    with ts.exact():
        train = ts.tensortrain(shape, p)
    recon = train.to_tensor()
    recon_err = float(np.linalg.norm(recon - p))

    return {
        "nsites": n,
        "state_count": int(2**n),
        "complete_edge_count": len(edges),
        "steps": params.steps,
        "positive_q_min": float(q.min()),
        "positive_q_max": float(q.max()),
        "final_probability_sum": float(p.sum()),
        "final_probability_min": float(p.min()),
        "final_entropy": history[-1]["entropy"],
        "final_free_energy": history[-1]["free_energy"],
        "initial_theta_norm": history[0]["theta_norm"],
        "final_theta_norm": history[-1]["theta_norm"],
        "qtt_core_shapes": [tuple(int(x) for x in core.shape) for core in train.cores],
        "qtt_reconstruction_error": recon_err,
        "history": history,
    }


def main() -> None:
    result = run_flow(FlowParams())
    print(json.dumps(result, indent=2))
    assert result["nsites"] == 6
    assert result["state_count"] == 64
    assert result["complete_edge_count"] == 15
    assert result["steps"] == 12
    assert result["positive_q_min"] > 0.0
    assert abs(result["final_probability_sum"] - 1.0) < 1e-12
    assert result["final_probability_min"] > 0.0
    assert result["qtt_reconstruction_error"] < 1e-12
    print("Boltzmann lnQ tensor-flow toy audit passed")


if __name__ == "__main__":
    main()

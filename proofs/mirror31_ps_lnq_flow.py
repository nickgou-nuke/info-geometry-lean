#!/usr/bin/env python3
"""31P/31S mirror-nucleus ln(Q) Boltzmann-flow toy.

External numerical witness only.  This script specializes the complete-graph
ln(Q) flow idea to the mirror pair

    31P: Z=15, N=16, Tz=(N-Z)/2=+1/2
    31S: Z=16, N=15, Tz=(N-Z)/2=-1/2

It uses 31 binary node variables as a coarse spin/isospin toy, but avoids dense
`2^31` enumeration.  Instead it evolves a mean-field complete-graph Boltzmann
approximation and stores the final factorized probability amplitude as a rank-1
quantics tensor train with 31 binary cores via trainsum.

No claim of physical nuclear spectroscopy is certified here; this is a socketed
numerical toy for the Lean bookkeeping layer.

Run:
    cd /home/goutev/auto
    external/repos/trainsum/.venv/bin/python proofs/mirror31_ps_lnq_flow.py
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
class MirrorNucleus:
    name: str
    Z: int
    N: int

    @property
    def A(self) -> int:
        return self.Z + self.N

    @property
    def Tz_twice(self) -> int:
        return self.N - self.Z

    @property
    def coulomb_pairs(self) -> int:
        return self.Z * (self.Z - 1) // 2


@dataclass(frozen=True)
class FlowParams:
    beta: float = 1.15
    coupling: float = 0.018
    dt: float = 0.06
    steps: int = 20
    damping: float = 0.35
    feedback: float = 0.16
    isospin_drive: float = 0.012


def complete_edge_count(n: int) -> int:
    return n * (n - 1) // 2


def local_q_table(nuc: MirrorNucleus) -> np.ndarray:
    """Positive two-state Q table for 31 coarse nucleon nodes.

    Proton-like nodes receive a slightly different tilt from neutron-like nodes,
    creating a mirror-asymmetric ln(Q) drive.  The model labels the first Z nodes
    as proton-like and the remaining N as neutron-like.
    """
    q = np.zeros((nuc.A, 2), dtype=float)
    for i in range(nuc.A):
        is_proton = i < nuc.Z
        shell_mod = (i % 5) / 100.0
        base = 1.22 + 0.015 * i + shell_mod
        tilt = (0.065 if is_proton else 0.045) + 0.002 * (i % 3)
        q[i, 0] = base - tilt
        q[i, 1] = base + tilt
    assert float(q.min()) > 0.0
    return q


def mean_field_flow(nuc: MirrorNucleus, params: FlowParams) -> dict[str, object]:
    n = nuc.A
    q = local_q_table(nuc)
    lnq_bias = 0.5 * (np.log(q[:, 1]) - np.log(q[:, 0]))
    lnq_mean = 0.5 * (np.log(q[:, 1]) + np.log(q[:, 0]))

    # θ starts as a small mirror/isospin gradient.
    idx = np.arange(n, dtype=float)
    proton_mask = np.where(idx < nuc.Z, 1.0, -1.0)
    theta = 0.10 * np.sin((idx + 1.0) * math.pi / (n + 1.0)) + params.isospin_drive * proton_mask
    target = float(lnq_mean.mean()) + 0.04 * proton_mask
    m = np.zeros(n, dtype=float)

    history = []
    for step in range(params.steps + 1):
        field = theta * lnq_bias + params.coupling * (float(m.sum()) - m)
        m = np.tanh(params.beta * field)
        p_plus = (1.0 + m) / 2.0
        entropy = float(-np.sum(p_plus * np.log(p_plus + 1e-300) + (1.0 - p_plus) * np.log(1.0 - p_plus + 1e-300)))
        expected_lnq = lnq_mean + m * lnq_bias
        feedback = -params.damping * theta + params.feedback * (target - expected_lnq)
        history.append(
            {
                "step": step,
                "theta_norm": float(np.linalg.norm(theta)),
                "mean_magnetization": float(m.mean()),
                "entropy_sum": entropy,
                "expected_lnq_mean": float(expected_lnq.mean()),
            }
        )
        if step < params.steps:
            theta = theta + params.dt * feedback

    p_plus = (1.0 + m) / 2.0
    p_minus = 1.0 - p_plus
    local_norm_error = float(np.max(np.abs(p_plus + p_minus - 1.0)))

    # Rank-1 quantics tensor train for the factorized probability amplitude.
    ts = TrainSum(np)
    shape = ts.trainshape(2**n, mode="block")
    cores = [np.sqrt(np.array([p_minus[i], p_plus[i]], dtype=float)).reshape(1, 2, 1) for i in range(n)]
    train = ts.tensortrain(shape, cores)
    rank_max = max(int(core.shape[-1]) for core in train.cores[:-1]) if n > 1 else 1
    core_shapes = [tuple(int(x) for x in core.shape) for core in train.cores]

    return {
        "name": nuc.name,
        "Z": nuc.Z,
        "N": nuc.N,
        "A": nuc.A,
        "Tz_twice": nuc.Tz_twice,
        "state_count_log2": n,
        "complete_edge_count": complete_edge_count(n),
        "coulomb_pairs": nuc.coulomb_pairs,
        "q_min": float(q.min()),
        "q_max": float(q.max()),
        "steps": params.steps,
        "local_probability_norm_error": local_norm_error,
        "final_theta_norm": history[-1]["theta_norm"],
        "final_mean_magnetization": history[-1]["mean_magnetization"],
        "final_entropy_sum": history[-1]["entropy_sum"],
        "rank_max": rank_max,
        "qtt_core_count": len(train.cores),
        "qtt_first_core_shape": core_shapes[0],
        "qtt_last_core_shape": core_shapes[-1],
        "history_tail": history[-3:],
    }


def main() -> None:
    params = FlowParams()
    P31 = MirrorNucleus("31P", Z=15, N=16)
    S31 = MirrorNucleus("31S", Z=16, N=15)
    rp = mean_field_flow(P31, params)
    rs = mean_field_flow(S31, params)
    result = {
        "mirror_pair": "31P/31S",
        "P31": rp,
        "S31": rs,
        "mass_number_match": P31.A == S31.A == 31,
        "mirror_Tz_sum_twice": P31.Tz_twice + S31.Tz_twice,
        "delta_Z": S31.Z - P31.Z,
        "delta_coulomb_pairs_S_minus_P": S31.coulomb_pairs - P31.coulomb_pairs,
    }
    print(json.dumps(result, indent=2))

    assert result["mass_number_match"] is True
    assert result["mirror_Tz_sum_twice"] == 0
    assert result["delta_Z"] == 1
    assert result["delta_coulomb_pairs_S_minus_P"] == 15
    for r in (rp, rs):
        assert r["A"] == 31
        assert r["complete_edge_count"] == 465
        assert r["state_count_log2"] == 31
        assert r["q_min"] > 0.0
        assert r["local_probability_norm_error"] < 1e-12
        assert r["rank_max"] == 1
        assert r["qtt_core_count"] == 31
    print("31P/31S mirror lnQ flow toy audit passed")


if __name__ == "__main__":
    main()

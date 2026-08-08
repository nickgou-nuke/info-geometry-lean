#!/usr/bin/env python3
"""SymPy/Python formalization of LieFlow (CFM on Lie groups) steps 2–8.

Implements the loop semantics:
1) x1 ~ data, g ~ group sample,
2) x0 = g • x1,
3) A = log(g⁻¹) ∈ 𝔤,
4) x_t = exp(t^γ A) • x0,  γ>=1 (γ>1 for discrete-symmetry correction),
5) L_t(θ) = ||v_θ(x_t,t) - A||².
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Iterable

import sympy as sp
import numpy as np

# ---------------------------------------------------------------------------
# 1) SO(3) helper maps (lightweight / explicit)
# ---------------------------------------------------------------------------

def hat(v: sp.Matrix) -> sp.Matrix:
    v = sp.Matrix(v)
    if v.shape != (3, 1):
        raise ValueError("so3 hat expects 3-vector column")
    vx, vy, vz = v[0], v[1], v[2]
    return sp.Matrix([[0, -vz, vy], [vz, 0, -vx], [-vy, vx, 0]])


def so3_exp(v: sp.Matrix) -> sp.Matrix:
    """Rodrigues formula: Exp : so(3) -> SO(3)."""
    v = sp.Matrix(v)
    θ = sp.sqrt((v.T * v)[0])
    if θ == 0:
        return sp.eye(3)
    K = hat(v)
    return sp.eye(3) + sp.sin(θ) / θ * K + (1 - sp.cos(θ)) / (θ**2) * (K @ K)


def so3_log(R: sp.Matrix) -> sp.Matrix:
    """Principal log for SO(3) matrix in a numerical form."""
    M = np.array(sp.N(R), dtype=float)
    tr = float(np.trace(M))
    c = min(1.0, max(-1.0, (tr - 1.0) / 2.0))
    θ = np.arccos(c)
    if abs(θ) < 1e-12:
        return sp.Matrix([0.0, 0.0, 0.0])
    w = 1.0 / (2.0 * np.sin(θ)) * np.array([M[2, 1] - M[1, 2], M[0, 2] - M[2, 0], M[1, 0] - M[0, 1]])
    return sp.Matrix(w * θ)


def rot_from_axis_angle(axis: sp.Matrix, angle: float) -> np.ndarray:
    a = np.array(axis, dtype=float).reshape(3)
    n = np.linalg.norm(a)
    if n == 0:
        return np.eye(3)
    a = a / n
    K = np.array([[0.0, -a[2], a[1]], [a[2], 0.0, -a[0]], [-a[1], a[0], 0.0]])
    return np.eye(3) + np.sin(angle) * K + (1.0 - np.cos(angle)) * (K @ K)

# ---------------------------------------------------------------------------
# 2) Algorithmic primitives for steps 2–8
# ---------------------------------------------------------------------------

def power_time(t: float, gamma: float) -> float:
    """Discrete-symmetry correction schedule τ = t^γ."""
    return float(t ** gamma)


@dataclass(frozen=True)
class LieFlowSample:
    x1: np.ndarray        # data point
    x0: np.ndarray        # g • x1
    g: np.ndarray         # group sample
    A: sp.Matrix          # log(g⁻¹)
    t: float
    gamma: float

    @property
    def t_sched(self) -> float:
        return power_time(self.t, self.gamma)

    @property
    def xt(self) -> np.ndarray:
        """Step 7 trajectory x_t = exp(t^γ A) • x0."""
        a = np.array(self.A, dtype=float).reshape(3)
        R = rot_from_axis_angle(a, np.linalg.norm(a * self.t_sched))
        return R @ self.x0


def cfm_step(x1: np.ndarray, g: np.ndarray, t: float, gamma: float = 1.0) -> LieFlowSample:
    """Single training triple (x0, A, x_t) for given data point and group sample."""
    x1 = np.array(x1, dtype=float).reshape(3)
    x0 = g @ x1
    A = sp.Matrix(g.T)  # g^{-1}=g^T for SO(3)
    A = so3_log(A)
    return LieFlowSample(x1=x1, x0=x0, g=g, A=A, t=t, gamma=gamma)


def flow_loss(
    v: Callable[[np.ndarray, float], np.ndarray],
    sample: LieFlowSample,
) -> float:
    """Step-8 squared-norm loss at sampled trajectory time."""
    pred = np.array(v(sample.xt, sample.t), dtype=float).reshape(3)
    A = np.array(sample.A, dtype=float).reshape(3)
    return float(np.dot(pred - A, pred - A))


def batch_loss(
    v: Callable[[np.ndarray, float], np.ndarray],
    x1: np.ndarray,
    g: np.ndarray,
    times: Iterable[float],
    gamma: float,
) -> float:
    losses = [
        flow_loss(v, cfm_step(x1, g, float(t), gamma))
        for t in times
    ]
    return float(np.mean(losses)) if losses else 0.0


# ---------------------------------------------------------------------------
# 3) Symbolic loss formula and gradients (step-8, power-time)
# ---------------------------------------------------------------------------

def symbolic_step8_loss() -> None:
    # x_t and A = (a1,a2,a3) are coordinates in algebra
    t, gamma = sp.symbols("t gamma", real=True)
    x1, x2, x3 = sp.symbols("x1 x2 x3", real=True)
    a1, a2, a3 = sp.symbols("a1 a2 a3", real=True)
    c1, c2, c3 = sp.symbols("c1 c2 c3", real=True)   # velocity params

    s = t ** gamma
    # Example parametric field: v_θ = c_i * x_i + s
    v = sp.Matrix([c1 * x1 + s, c2 * x2 + s, c3 * x3 + s])
    A = sp.Matrix([a1, a2, a3])
    L = sp.expand((v - A)[0]**2 + (v - A)[1]**2 + (v - A)[2]**2)

    print("=== SymPy: symbolic step-8 with power-time ===")
    print("L(t) =", L)
    print("∂L/∂t =", sp.expand(sp.diff(L, t)))
    print("(note chain factor γ t^(γ-1) is inside d/dt of t^γ)")
    print("∂L/∂c1 =", sp.expand(sp.diff(L, c1)))
    print("∂L/∂c2 =", sp.expand(sp.diff(L, c2)))
    print("∂L/∂c3 =", sp.expand(sp.diff(L, c3)))


def run_demo() -> None:
    print("=== LieFlow symbolic/ numerical demo ===")
    symbolic_step8_loss()

    x1 = np.array([1.0, 0.0, 0.0])
    g = rot_from_axis_angle(sp.Matrix([0, 0, 1]), 0.9)
    times = [0.25, 0.5, 0.75, 0.9, 1.0]

    # Zero predictor gives nonzero loss, constant predictor = A gives zero loss
    sample = cfm_step(x1, g, 0.5, gamma=1.4)
    print("A =", np.array(sample.A, dtype=float))

    def v_const(_x, _t):
        return np.array(sample.A, dtype=float).reshape(3)

    print("Batch loss (γ=1.4, v ≡ A):", batch_loss(v_const, x1, g, times, gamma=1.4))


if __name__ == "__main__":
    run_demo()

"""Shape–Sinkhorn–detector factors and a guarded bipartite Poisson solve.

Adapted from the two supplied 2026-10-23 notes. Finite Sinkhorn iterations do
not imply exact bistochasticity. Reconstruction and the balanced log-gauge
are algebraic identities; reported residuals measure floating-point error.
The solver rejects unbalanced, disconnected, or unresolved near-singular
cores rather than silently regularizing the operator. Autograd differentiates
the executed operations; numerical diagnostics are not Lean proof checks.
"""
from __future__ import annotations

import math
from typing import Literal

import torch
from torch import Tensor, nn


def _finite_real(x: Tensor, name: str) -> None:
    if not isinstance(x, Tensor) or x.dtype not in (torch.float32, torch.float64):
        raise TypeError(f"{name} must be a float32 or float64 tensor")
    if not bool(torch.isfinite(x.detach()).all()):
        raise ValueError(f"{name} must be finite")


def _square(x: Tensor, name: str) -> int:
    _finite_real(x, name)
    if x.ndim < 2 or x.shape[-1] < 1 or x.shape[-2] != x.shape[-1]:
        raise ValueError(f"{name} must have nonempty square trailing dimensions")
    return x.shape[-1]


def _tolerance(x: Tensor, tol: float | None) -> float:
    value = (1e-10 if x.dtype == torch.float64 else 2e-5) if tol is None else tol
    if not math.isfinite(value) or value <= 0:
        raise ValueError("tolerance must be finite and positive")
    return value


def differentiable_sinkhorn_core_decomposition(
    log_S: Tensor, n_iters: int = 100, *, tolerance: float | None = None,
) -> tuple[Tensor, Tensor, Tensor, Tensor, dict[str, Tensor]]:
    """Return gains, core B, reconstructed S, and per-batch diagnostics.

    Executes exactly n_iters updates, retaining the differentiation graph.
    A convergence flag is returned, never inferred from the iteration count.
    The returned B is not clipped, renormalized, or substituted afterward.
    """
    _square(log_S, "log_S")
    if isinstance(n_iters, bool) or not isinstance(n_iters, int) or n_iters < 1:
        raise ValueError("n_iters must be a positive integer")
    tol = _tolerance(log_S, tolerance)
    u = torch.zeros_like(log_S[..., :, 0])
    v = torch.zeros_like(log_S[..., 0, :])
    for _ in range(n_iters):
        u = -torch.logsumexp(log_S + v.unsqueeze(-2), dim=-1)
        v = -torch.logsumexp(log_S + u.unsqueeze(-1), dim=-2)
    gamma = 0.5 * (u.mean(-1, keepdim=True) - v.mean(-1, keepdim=True))
    log_shape, log_det = -u + gamma, -v - gamma
    log_B = log_S - log_shape.unsqueeze(-1) - log_det.unsqueeze(-2)
    B, a, b = log_B.exp(), log_shape.exp(), log_det.exp()
    S_recon = a.unsqueeze(-1) * B * b.unsqueeze(-2)
    for name, value in (("B", B), ("shape gains", a), ("detector gains", b),
                        ("S reconstruction", S_recon)):
        if not bool((torch.isfinite(value.detach()) & (value.detach() > 0)).all()):
            raise FloatingPointError(f"{name} overflowed or underflowed; rescale logits or use float64")
    phi = log_B - log_B.mean(-1, keepdim=True) - log_B.mean(-2, keepdim=True)
    phi = phi + log_B.mean((-2, -1), keepdim=True)
    with torch.no_grad():
        row_error = (B.sum(-1) - 1).abs().amax(-1)
        col_error = (B.sum(-2) - 1).abs().amax(-1)
        error = torch.maximum(row_error, col_error)
        log_residual = (log_shape.unsqueeze(-1) + log_B + log_det.unsqueeze(-2) - log_S).abs().amax((-2, -1))
        gauge_error = (log_shape.mean(-1) - log_det.mean(-1)).abs()
        reconstruction_error = torch.linalg.matrix_norm(S_recon - log_S.exp())
    return a, B, b, S_recon, {
        "log_B": log_B, "log_shape_gain": log_shape, "log_detector_gain": log_det,
        "phi_copula": phi, "row_error": row_error, "column_error": col_error,
        "bistochastic_error": error, "sinkhorn_converged": error <= tol,
        "log_reconstruction_error": log_residual, "balanced_log_gauge_error": gauge_error,
        "core_reconstruction_error": reconstruction_error,
    }


class BistochasticBipartiteLaplacianSolver(nn.Module):
    """Connected-core solver with explicit odd-mean correction.

    Symmetry alone does not make L+Pi invertible. The smallest eigenvalue of
    I-BB^T+Pi (and its right analogue) must exceed the requested gap tolerance.
    This also excludes permutation cores with multiple disconnected pairs.
    Validation uses detached values; it is not a surrogate backward pass.
    """
    def __init__(self, method: Literal["gramian_schur", "full_2k"] = "gramian_schur",
                 *, tolerance: float | None = None, gap_tolerance: float | None = None):
        super().__init__()
        if method not in ("gramian_schur", "full_2k"):
            raise ValueError("unknown solver method")
        if gap_tolerance is not None and (not math.isfinite(gap_tolerance) or gap_tolerance <= 0):
            raise ValueError("gap_tolerance must be finite and positive")
        self.method, self.tolerance, self.gap_tolerance = method, tolerance, gap_tolerance

    @staticmethod
    def build_bipartite_matrices(B: Tensor) -> tuple[Tensor, Tensor, Tensor, Tensor]:
        k = _square(B, "B")
        z, bt = torch.zeros_like(B), B.transpose(-2, -1)
        lift = torch.cat((torch.cat((z, B), -1), torch.cat((bt, z), -1)), -2)
        return lift, torch.eye(2*k, dtype=B.dtype, device=B.device) - lift, B @ bt, bt @ B

    def forward(self, B: Tensor, b_shape: Tensor, b_det: Tensor,
                *, return_diagnostics: bool = True) -> tuple[Tensor, Tensor, dict[str, Tensor]]:
        k = _square(B, "B")
        for name, rhs in (("b_shape", b_shape), ("b_det", b_det)):
            _finite_real(rhs, name)
            if rhs.ndim < 2 or rhs.shape[-2] != k or rhs.shape[-1] < 1:
                raise ValueError(f"{name} needs trailing shape (K, D), D > 0")
            if rhs.dtype != B.dtype or rhs.device != B.device:
                raise ValueError("B and signals must use the same dtype and device")
        if b_shape.shape != b_det.shape:
            raise ValueError("shape and detector signals must have identical shapes")
        torch.broadcast_shapes(B.shape[:-2], b_shape.shape[:-2])
        tol = _tolerance(B, self.tolerance)
        bt = B.transpose(-2, -1)
        eye = torch.eye(k, dtype=B.dtype, device=B.device)
        pi = torch.ones_like(eye) / k
        left, right = eye - B @ bt + pi, eye - bt @ B + pi
        with torch.no_grad():
            if bool((B < 0).any()):
                raise ValueError("B must be entrywise nonnegative")
            err = torch.maximum((B.sum(-1)-1).abs().amax(-1), (B.sum(-2)-1).abs().amax(-1))
            if bool((err > tol).any()):
                raise ValueError("B is not bistochastic within tolerance; increase Sinkhorn iterations")
            gap = torch.minimum(torch.linalg.eigvalsh(left)[..., 0],
                                torch.linalg.eigvalsh(right)[..., 0])
            gap_tol = self.gap_tolerance or (100 * k * torch.finfo(B.dtype).eps)
            if bool((gap <= gap_tol).any()):
                raise ValueError("Disconnected or numerically unresolved core: rank-one stationary solver is invalid")
        mu_s, mu_d = b_shape.mean(-2, keepdim=True), b_det.mean(-2, keepdim=True)
        delta = 0.5 * (mu_s - mu_d)
        if self.method == "gramian_schur":
            zs = torch.linalg.solve(left, b_shape - mu_s)
            zd = torch.linalg.solve(right, b_det - mu_d)
            xs, xd = zs + B @ zd + 0.5 * delta, bt @ zs + zd - 0.5 * delta
        else:
            _, lap, _, _ = self.build_bipartite_matrices(B)
            pi2 = torch.ones((2*k, 2*k), dtype=B.dtype, device=B.device) / (2*k)
            rhs = torch.cat((b_shape, b_det), -2)
            x = torch.linalg.solve(lap + pi2, rhs - rhs.mean(-2, keepdim=True))
            xs, xd = x[..., :k, :], x[..., k:, :]
        _finite_real(xs, "shape solution")
        _finite_real(xd, "detector solution")
        diagnostics = {}
        if return_diagnostics:
            with torch.no_grad():
                grand = 0.5 * (mu_s + mu_d)
                residual = torch.cat((xs - B @ xd - b_shape + grand,
                                      xd - bt @ xs - b_det + grand), -2)
                diagnostics = {
                    "bistochastic_error": err, "minimum_gramian_system_eigenvalue": gap,
                    "poisson_residual": torch.linalg.matrix_norm(residual),
                    "centering_error": torch.cat((xs, xd), -2).mean(-2).abs().amax(-1),
                }
        return xs, xd, diagnostics


class FiveFactorShapeSinkhornDetector(nn.Module):
    """Learnable response factors and a positive square latent core.

    This parameterizes a model C_hat, not a universal unique low-rank
    factorization of an arbitrary empirical C. Feature encoding uses U^T,V^T;
    it is not claimed to be an inverse to response decoding.
    """
    def __init__(self, num_shapes: int, num_detectors: int, num_channels: int,
                 sinkhorn_iters: int = 100, solver_method: str = "gramian_schur",
                 *, tolerance: float | None = None):
        super().__init__()
        if any(isinstance(n, bool) or not isinstance(n, int) or n < 1
               for n in (num_shapes, num_detectors, num_channels, sinkhorn_iters)):
            raise ValueError("dimensions and iteration count must be positive integers")
        self.sinkhorn_iters, self.tolerance = sinkhorn_iters, tolerance
        self.shape_logits = nn.Parameter(torch.randn(num_shapes, num_channels) * 0.1)
        self.detector_logits = nn.Parameter(torch.randn(num_detectors, num_channels) * 0.1)
        self.core_logits = nn.Parameter(torch.randn(num_channels, num_channels) * 0.1)
        self.bipartite_solver = BistochasticBipartiteLaplacianSolver(solver_method, tolerance=tolerance)

    def forward(self, shape_features: Tensor | None = None,
                detector_features: Tensor | None = None) -> dict[str, Tensor]:
        if (shape_features is None) != (detector_features is None):
            raise ValueError("provide both feature tables or neither")
        U, V = self.shape_logits.softmax(0), self.detector_logits.softmax(0)
        a, B, b, S, info = differentiable_sinkhorn_core_decomposition(
            self.core_logits, self.sinkhorn_iters, tolerance=self.tolerance)
        C = (U * a.unsqueeze(0)) @ B @ (V * b.unsqueeze(0)).transpose(-2, -1)
        out = {"C_recon": C, "U": U, "V": V, "d_shape": a, "d_det": b, "B": B,
               "S_core": S, "row_marginal": U @ S.sum(-1),
               "col_marginal": V @ S.sum(-2), **info}
        if shape_features is not None:
            assert detector_features is not None
            xs, xd, diag = self.bipartite_solver(B, U.T @ shape_features, V.T @ detector_features)
            out.update(shape_response_out=U @ xs, detector_response_out=V @ xd,
                       x_shape_latent=xs, x_det_latent=xd, **diag)
        return out

    def loss_function(self, C_target: Tensor, L_shape_graph: Tensor | None = None,
                      L_det_graph: Tensor | None = None, gamma_shape: float = 1e-2,
                      gamma_det: float = 1e-2) -> tuple[Tensor, dict[str, Tensor]]:
        out = self()
        estimate = out["C_recon"]
        _finite_real(C_target, "C_target")
        if (C_target.shape != estimate.shape or C_target.dtype != estimate.dtype
                or C_target.device != estimate.device or bool((C_target.detach() < 0).any())):
            raise ValueError("counts must be nonnegative and match the model's shape/dtype/device")
        if min(gamma_shape, gamma_det) < 0 or not all(map(math.isfinite, (gamma_shape, gamma_det))):
            raise ValueError("regularization weights must be finite and nonnegative")
        _finite_real(estimate, "C_recon")
        if bool((estimate.detach() <= 0).any()):
            raise FloatingPointError("predicted counts must remain positive")
        # 0 log 0 = 0: observed zeros are not replaced by invented counts.
        kl = (torch.xlogy(C_target, C_target) - C_target * estimate.log() - C_target + estimate).sum()
        reg = torch.zeros_like(kl)
        for L, response, weight in ((L_shape_graph, out["U"], gamma_shape),
                                     (L_det_graph, out["V"], gamma_det)):
            if L is not None:
                _square(L, "graph Laplacian")
                if L.shape != (response.shape[0], response.shape[0]):
                    raise ValueError("graph Laplacian has incompatible dimensions")
                reg = reg + weight * torch.trace(response.T @ L @ response)
        return kl + reg, {"kl_loss": kl.detach(), "reg_loss": reg.detach()}

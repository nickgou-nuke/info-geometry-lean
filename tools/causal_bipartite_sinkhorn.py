"""Prefix-local latent bipartite response, following the three supplied notes.

Uses PR #199's guarded Sinkhorn and Poisson owners unchanged. Block-causal
mode is bidirectional within a chunk. Strict-token mode solves separately
for each detector prefix and never reads a completed current-chunk summary.
This is a new attention architecture, not a numerical replacement for SDPA.
No dense chunk-by-chunk weight tensor, artificial padded tokens, Tikhonov
floor, custom backward, or detached activation cache is introduced.
"""
from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Literal

import torch
from torch import Tensor, nn

from tools.shape_sinkhorn_detector import (
    BistochasticBipartiteLaplacianSolver,
    differentiable_sinkhorn_core_decomposition,
)


@dataclass(frozen=True)
class PoolState:
    log_mass: Tensor
    keys: Tensor
    values: Tensor


def _check_tensor(x: Tensor, name: str) -> None:
    if not isinstance(x, Tensor) or x.dtype not in (torch.float32, torch.float64):
        raise TypeError(f"{name} must be float32 or float64")
    if not bool(torch.isfinite(x.detach()).all()):
        raise ValueError(f"{name} must be finite")


def masked_column_pool(logits: Tensor, keys: Tensor, values: Tensor,
                       valid: Tensor) -> PoolState:
    """Pool a finite block; all-masked blocks have zero output and mass zero.

    logits (..., L, K), keys/values (..., L, D), valid broadcastable to
    (..., L). Valid logits must be finite. No finite sentinel represents -inf.
    """
    for name, x in (("logits", logits), ("keys", keys), ("values", values)):
        _check_tensor(x, name)
    if logits.ndim < 2 or min(logits.shape[-2:]) < 1:
        raise ValueError("pool dimensions must be nonempty")
    if keys.shape != values.shape or keys.shape[:-1] != logits.shape[:-1]:
        raise ValueError("pool shapes are incompatible")
    if valid.dtype != torch.bool or valid.device != logits.device:
        raise TypeError("valid must be a boolean mask on the tensor device")
    if keys.dtype != logits.dtype or keys.device != logits.device or values.dtype != logits.dtype or values.device != logits.device:
        raise ValueError("pool tensors must share dtype/device")
    mask = torch.broadcast_to(valid, logits.shape[:-1]).unsqueeze(-1)
    selected = logits.masked_fill(~mask, -torch.inf)
    maximum = selected.amax(-2, keepdim=True)
    safe_maximum = torch.where(torch.isfinite(maximum), maximum, torch.zeros_like(maximum))
    weight = (selected - safe_maximum).exp()
    mass = weight.sum(-2, keepdim=True)
    denominator = torch.where(mass > 0, mass, torch.ones_like(mass))
    weight = weight / denominator
    log_mass = (safe_maximum + denominator.log()).squeeze(-2)
    log_mass = log_mass.masked_fill(~mask.any(-2), -torch.inf)
    return PoolState(log_mass, weight.transpose(-2, -1) @ keys,
                     weight.transpose(-2, -1) @ values)


def merge_pools(a: PoolState | None, b: PoolState) -> PoolState:
    """Stable exact-real union identity, retaining autograd across all blocks."""
    if a is None:
        return b
    maximum = torch.maximum(a.log_mass, b.log_mass)
    base = torch.where(torch.isfinite(maximum), maximum, torch.zeros_like(maximum))
    u, v = (a.log_mass - base).exp(), (b.log_mass - base).exp()
    z = u + v
    safe_z = torch.where(z > 0, z, torch.ones_like(z))
    u, v = (u / safe_z).unsqueeze(-1), (v / safe_z).unsqueeze(-1)
    log_mass = (base + safe_z.log()).masked_fill(z == 0, -torch.inf)
    return PoolState(log_mass, u * a.keys + v * b.keys,
                     u * a.values + v * b.values)


def five_factor_conditional(U: Tensor, V: Tensor, a: Tensor, B: Tensor,
                            b: Tensor, values: Tensor) -> Tensor:
    """Normalized C^T value readout for C=U diag(a) B diag(b) V^T.

    U is column-normalized. This helper uses O((Nk+Nq)Kd+K^2d) work
    and does not materialize C. Positivity/nonempty rows are required.
    """
    for name, x in (("U", U), ("V", V), ("a", a), ("B", B), ("b", b), ("values", values)):
        _check_tensor(x, name)
    if any(bool((x.detach() < 0).any()) for x in (U, V, a, B, b)):
        raise ValueError("factor entries must be nonnegative")
    if not torch.allclose(U.sum(-2), torch.ones_like(a), atol=1e-6, rtol=1e-6):
        raise ValueError("U must be column-normalized")
    pooled = U.transpose(-2, -1) @ values
    r = (B.transpose(-2, -1) @ a.unsqueeze(-1)).squeeze(-1)
    if bool((r.detach() <= 0).any()):
        raise ValueError("all detector channel masses must be positive")
    z = (B.transpose(-2, -1) @ (a.unsqueeze(-1) * pooled)) / r.unsqueeze(-1)
    weights = V * (b * r).unsqueeze(-2)
    mass = weights.sum(-1, keepdim=True)
    if bool((mass.detach() <= 0).any()):
        raise ValueError("all query masses must be positive")
    return (weights / mass) @ z


class MultiHeadBipartiteSinkhornAttention(nn.Module):
    """Bidirectional self/cross latent-channel response with two direct modes.

    balanced: the attachment's B^T pooled-value branch (not full C readout).
    five_factor: normalized C^T readout including the shape-gain correction.
    The Poisson branch is signed and is not a probability-weighted readout.
    """
    def __init__(self, d_model: int, n_heads: int, num_channels: int = 16,
                 sinkhorn_iters: int = 100, tau: float = 1.0,
                 poisson_mix_init: float = 0.5, dropout: float = 0.0,
                 direct_mode: Literal["balanced", "five_factor"] = "balanced",
                 solver_method: str = "gramian_schur", tolerance: float | None = None):
        super().__init__()
        for n in (d_model, n_heads, num_channels, sinkhorn_iters):
            if isinstance(n, bool) or not isinstance(n, int) or n < 1:
                raise ValueError("dimensions and iteration count must be positive integers")
        if d_model % n_heads:
            raise ValueError("d_model must be divisible by n_heads")
        if not math.isfinite(tau) or tau <= 0:
            raise ValueError("tau must be finite and positive")
        if not 0 < poisson_mix_init < 1 or not 0 <= dropout < 1:
            raise ValueError("gate probability must be in (0,1); dropout in [0,1)")
        if direct_mode not in ("balanced", "five_factor"):
            raise ValueError("unknown direct mode")
        self.d_model, self.n_heads = d_model, n_heads
        self.d_head, self.num_channels = d_model // n_heads, num_channels
        self.sinkhorn_iters, self.tau, self.tolerance = sinkhorn_iters, tau, tolerance
        self.direct_mode = direct_mode
        self.q_proj = nn.Linear(d_model, d_model)
        self.k_proj = nn.Linear(d_model, d_model)
        self.v_shape_proj = nn.Linear(d_model, d_model)
        self.v_det_proj = nn.Linear(d_model, d_model)
        self.out_proj = nn.Linear(d_model, d_model)
        scale = self.d_head ** -0.5
        self.W_shape = nn.Parameter(torch.randn(n_heads, self.d_head, num_channels) * scale)
        self.W_det = nn.Parameter(torch.randn(n_heads, self.d_head, num_channels) * scale)
        self.core_log_prior = nn.Parameter(torch.eye(num_channels).expand(n_heads, -1, -1).clone())
        self.poisson_gate = nn.Parameter(torch.full((n_heads, 1, 1), math.log(poisson_mix_init / (1 - poisson_mix_init))))
        self.solver = BistochasticBipartiteLaplacianSolver(solver_method, tolerance=tolerance)
        # Apply dropout after readout, not to the normalized responsibilities.
        self.dropout = nn.Dropout(dropout)

    def _validate(self, x: Tensor, mask: Tensor | None) -> Tensor:
        _check_tensor(x, "input")
        if x.ndim != 3 or x.shape[1] == 0 or x.shape[-1] != self.d_model:
            raise ValueError("input must have shape (batch, nonempty sequence, d_model)")
        if mask is None:
            return torch.ones(x.shape[:2], dtype=torch.bool, device=x.device)
        if mask.shape != x.shape[:2] or mask.dtype != torch.bool or mask.device != x.device:
            raise ValueError("padding mask must be boolean (batch, sequence) on input device")
        return ~mask

    def _project(self, x: Tensor, layer: nn.Module) -> Tensor:
        return layer(x).reshape(x.shape[0], x.shape[1], self.n_heads, self.d_head).transpose(1, 2)

    def _read(self, shape: PoolState, det: PoolState, logits: Tensor,
              diagnostics: bool) -> tuple[Tensor, dict[str, Tensor]]:
        log_s = shape.keys @ det.keys.transpose(-2, -1) / (math.sqrt(self.d_head) * self.tau)
        log_s = log_s + self.core_log_prior
        a, core, b, _, info = differentiable_sinkhorn_core_decomposition(
            log_s, self.sinkhorn_iters, tolerance=self.tolerance)
        _, xd, solver_info = self.solver(core, shape.values, det.values,
                                         return_diagnostics=diagnostics)
        finite_mass = torch.where(torch.isfinite(det.log_mass), det.log_mass,
                                  torch.zeros_like(det.log_mass))
        log_v = logits - finite_mass.unsqueeze(-2)
        responsibility = (log_v + info["log_detector_gain"].unsqueeze(-2)).softmax(-1)
        poisson = responsibility @ xd
        if self.direct_mode == "balanced":
            direct = responsibility @ (core.transpose(-2, -1) @ shape.values)
        else:
            r = (core.transpose(-2, -1) @ a.unsqueeze(-1)).squeeze(-1)
            z = (core.transpose(-2, -1) @ (a.unsqueeze(-1) * shape.values)) / r.unsqueeze(-1)
            full_r = (log_v + (info["log_detector_gain"] + r.log()).unsqueeze(-2)).softmax(-1)
            direct = full_r @ z
        gate = self.poisson_gate.sigmoid()
        out = (1-gate) * direct + gate * poisson
        if not diagnostics:
            return out, {}
        diag = {"bistochastic_error": info["bistochastic_error"].detach(), **solver_info}
        return out, diag

    def _finish(self, heads: Tensor, valid: Tensor) -> Tensor:
        y = heads.transpose(1, 2).reshape(valid.shape[0], valid.shape[1], self.d_model)
        return self.out_proj(self.dropout(y)).masked_fill(~valid.unsqueeze(-1), 0)

    def forward(self, x_q: Tensor, x_kv: Tensor | None = None,
                key_padding_mask: Tensor | None = None,
                query_padding_mask: Tensor | None = None,
                return_diagnostics: bool = False) -> tuple[Tensor, dict[str, Tensor]]:
        self_attention = x_kv is None
        if x_kv is None:
            x_kv = x_q
        if query_padding_mask is None and self_attention:
            query_padding_mask = key_padding_mask
        qvalid, kvalid = self._validate(x_q, query_padding_mask), self._validate(x_kv, key_padding_mask)
        if not bool(kvalid.any(-1).all()):
            raise ValueError("bidirectional attention requires a valid key in each sample")
        if x_q.shape[0] != x_kv.shape[0] or x_q.dtype != x_kv.dtype or x_q.device != x_kv.device:
            raise ValueError("queries and keys must share batch, dtype and device")
        q, k = self._project(x_q, self.q_proj), self._project(x_kv, self.k_proj)
        vs, vd = self._project(x_kv, self.v_shape_proj), self._project(x_q, self.v_det_proj)
        sl = torch.einsum("bhnd,hdk->bhnk", k, self.W_shape) / math.sqrt(self.d_head)
        dl = torch.einsum("bhnd,hdk->bhnk", q, self.W_det) / math.sqrt(self.d_head)
        shape = masked_column_pool(sl, k, vs, kvalid[:, None, :])
        det = masked_column_pool(dl, q, vd, qvalid[:, None, :])
        heads, diag = self._read(shape, det, dl, return_diagnostics)
        return self._finish(heads, qvalid), diag


class BlockCausalMultiHeadBipartiteSinkhornAttention(MultiHeadBipartiteSinkhornAttention):
    """Block-local or strictly token-local self attention.

    Block mode: one latent core/solve per chunk, including that whole chunk.
    Strict mode: completed earlier chunks on the shape side; detector prefixes
    and a separate core/solve at each current token; local causal dot-product
    attention inside the chunk. No history means local attention alone.
    The reference implementation is sequential, not a fused GPU kernel.
    """
    def __init__(self, d_model: int, n_heads: int, num_channels: int = 16,
                 chunk_size: int = 32, causal_mode: str = "block_causal", **kwargs):
        super().__init__(d_model, n_heads, num_channels, **kwargs)
        if isinstance(chunk_size, bool) or not isinstance(chunk_size, int) or chunk_size < 1:
            raise ValueError("chunk_size must be a positive integer")
        if causal_mode not in ("block_causal", "strict_token_causal"):
            raise ValueError("unknown causality mode")
        self.chunk_size, self.causal_mode = chunk_size, causal_mode
        self.intra_chunk_gate = nn.Parameter(torch.zeros(n_heads, 1, 1))

    def forward(self, x: Tensor, key_padding_mask: Tensor | None = None,
                return_diagnostics: bool = False) -> tuple[Tensor, dict[str, Tensor]]:
        valid = self._validate(x, key_padding_mask)
        q, k = self._project(x, self.q_proj), self._project(x, self.k_proj)
        vs, vd = self._project(x, self.v_shape_proj), self._project(x, self.v_det_proj)
        sl = torch.einsum("bhnd,hdk->bhnk", k, self.W_shape) / math.sqrt(self.d_head)
        dl = torch.einsum("bhnd,hdk->bhnk", q, self.W_det) / math.sqrt(self.d_head)
        history: PoolState | None = None
        outputs, records = [], []
        for start in range(0, x.shape[1], self.chunk_size):
            end = min(start+self.chunk_size, x.shape[1])
            block = slice(start, end)
            current = masked_column_pool(sl[..., block, :], k[..., block, :],
                                         vs[..., block, :], valid[:, None, block])
            if self.causal_mode == "block_causal":
                history = merge_pools(history, current)
                det = masked_column_pool(dl[..., block, :], q[..., block, :],
                                         vd[..., block, :], valid[:, None, block])
                y, info = self._read(history, det, dl[..., block, :], return_diagnostics)
                outputs.append(y)
                if return_diagnostics:
                    records.append(info)
                continue
            detector: PoolState | None = None
            for pos in range(start, end):
                token = slice(pos, pos+1)
                detector = merge_pools(detector, masked_column_pool(
                    dl[..., token, :], q[..., token, :], vd[..., token, :], valid[:, None, token]))
                local_keys, local_vals = k[..., start:pos+1, :], vs[..., start:pos+1, :]
                score = (q[..., token, :] @ local_keys.transpose(-2, -1)) / math.sqrt(self.d_head)
                local_mask = valid[:, None, None, start:pos+1]
                selected = score.masked_fill(~local_mask, -torch.inf)
                mx = selected.amax(-1, keepdim=True)
                mx = torch.where(torch.isfinite(mx), mx, torch.zeros_like(mx))
                weights = (selected-mx).exp()
                den = weights.sum(-1, keepdim=True)
                local = (weights / torch.where(den > 0, den, torch.ones_like(den))) @ local_vals
                if history is None:
                    y = local
                else:
                    hist, info = self._read(history, detector, dl[..., token, :], return_diagnostics)
                    has_past = torch.isfinite(history.log_mass).any(-1)[..., None, None]
                    mix = self.intra_chunk_gate.sigmoid()
                    y = torch.where(has_past, mix*hist + (1-mix)*local, local)
                    if return_diagnostics:
                        records.append(info)
                outputs.append(y)
            history = merge_pools(history, current)
        diag = {}
        if return_diagnostics:
            for name in ("bistochastic_error", "poisson_residual", "centering_error"):
                diag[name] = torch.stack([r[name].amax() for r in records]).amax() if records else x.new_tensor(0.)
            diag["number_of_latent_solves"] = x.new_tensor(len(records))
        return self._finish(torch.cat(outputs, -2), valid), diag

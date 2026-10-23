"""Logging-only route diagnostics with explicit retained and residual output.

Dense top-K peeling costs O(K*n^2); the subsequent graph analysis is O(K*n).
No backpropagation replacement, GPU speedup, or graph-depth/reasoning claim.
"""
from __future__ import annotations
from dataclasses import dataclass
import math
import torch
from torch import nn
from .functional_route_fibers import analyze_route


@dataclass(frozen=True)
class RoutePeeling:
    routes: torch.Tensor
    weights: torch.Tensor
    residual: torch.Tensor


@torch.no_grad()
def peel_routes(P: torch.Tensor, top_k: int = 4, *, atol: float | None = None) -> RoutePeeling:
    if P.ndim < 2 or P.shape[-1] != P.shape[-2] or P.shape[-1] == 0:
        raise ValueError('Expected (..., n, n), n>0; rectangular routes are not endomorphisms.')
    if P.dtype not in (torch.float32, torch.float64):
        raise ValueError('Use float32 or float64 explicitly for the diagnostic snapshot.')
    if isinstance(top_k, bool) or not isinstance(top_k, int) or top_k < 0:
        raise ValueError('top_k must be a nonnegative integer.')
    tolerance = (1e-6 if P.dtype == torch.float32 else 1e-12) if atol is None else atol
    if not math.isfinite(tolerance) or tolerance < 0:
        raise ValueError('atol must be finite and nonnegative.')
    if not bool(torch.isfinite(P).all()) or bool((P < 0).any()):
        raise ValueError('Attention must be finite and entrywise nonnegative.')
    if bool((torch.abs(P.sum(-1) - 1) > tolerance).any()):
        raise ValueError('Rows must sum to one within atol; normalization is not implicit.')
    n = P.shape[-1]
    R = P.detach().clone()
    routes = torch.zeros((*P.shape[:-2], top_k, n), dtype=torch.long, device=P.device)
    weights = torch.zeros((*P.shape[:-2], top_k), dtype=P.dtype, device=P.device)
    for r in range(top_k):
        maximum, f = R.max(dim=-1)
        weight = maximum.min(dim=-1).values
        routes[..., r, :] = f
        weights[..., r] = weight
        R.scatter_add_(-1, f.unsqueeze(-1), -weight[..., None, None].expand(*f.shape, 1))
    # Do not clamp or silently repair arithmetic. The residual remains part of the output.
    if bool((R < 0).any()):
        raise ArithmeticError('Peeling produced negative residual entries.')
    return RoutePeeling(routes, weights, R)


class FunctionalRouteDiagnostics(nn.Module):
    """Snapshot analysis; all mixture statistics identify their conditioning.

    Route averages are coupling-dependent except explicitly named invariants.
    No leaf/relay/sink counts are labeled as Moore-Penrose eigenspaces.
    """
    def __init__(self, top_k_routes: int = 4):
        super().__init__()
        self.top_k_routes = top_k_routes

    @torch.no_grad()
    def forward(self, P: torch.Tensor, V: torch.Tensor | None = None) -> dict[str, torch.Tensor]:
        peeled = peel_routes(P, self.top_k_routes)
        n, shape = P.shape[-1], P.shape[:-2]
        batch_size = math.prod(shape)
        if batch_size == 0:
            raise ValueError('Empty batches are not supported.')
        K = self.top_k_routes
        routes = peeled.routes.reshape(batch_size, K, n)
        weights = peeled.weights.reshape(batch_size, K)
        mass = weights.sum(-1)
        raw_core = torch.zeros_like(mass)
        raw_depth = torch.zeros_like(mass)
        entry_hist = P.new_zeros((batch_size, n))
        rank_hist = P.new_zeros((batch_size, n))
        core_out = nil_out = None
        if V is not None:
            if (V.ndim != P.ndim or V.shape[:-2] != shape or V.shape[-2] != n or
                    V.shape[-1] == 0 or V.device != P.device or V.dtype != P.dtype):
                raise ValueError('V must have the same batch shape, dtype/device, and n rows as P.')
            if not bool(torch.isfinite(V).all()):
                raise ValueError('V must be finite.')
            values = V.reshape(batch_size, n, V.shape[-1])
            core_out = torch.zeros_like(values)
            nil_out = torch.zeros_like(values)
        route_lists = routes.cpu().tolist()
        for b in range(batch_size):
            for r in range(K):
                if weights[b, r].item() == 0:
                    continue
                g = analyze_route(route_lists[b][r])
                w = weights[b, r]
                raw_core[b] += w * len(g.recurrent) / n
                raw_depth[b] += w * g.index
                if g.index:
                    entry_hist[b, :g.index] += w * P.new_tensor(g.entry_depth_counts) / n
                    rank_hist[b, :g.index] += w * P.new_tensor(g.shell_ranks) / n
                if V is not None:
                    idx = torch.tensor([g.route[g.rho[i]] for i in range(n)],
                                       device=P.device, dtype=torch.long)
                    c = values[b].index_select(0, idx)
                    routed = values[b].index_select(0, routes[b, r])
                    core_out[b] += w * c
                    nil_out[b] += w * (routed - c)
        denominator = torch.where(mass > 0, mass, torch.full_like(mass, float('nan')))
        out = {
            'captured_mass': mass.reshape(shape),
            'residual_mass_per_query': peeled.residual.sum(-1),
            'retained_core_fraction_contribution': raw_core.reshape(shape),
            'conditional_core_fraction': (raw_core / denominator).reshape(shape),
            'conditional_route_index': (raw_depth / denominator).reshape(shape),
            'conditional_entry_depth_histogram': (entry_hist / denominator[:, None]).reshape(*shape, n),
            'conditional_shell_rank_histogram': (rank_hist / denominator[:, None]).reshape(*shape, n),
            'route_weights': peeled.weights,
            'routes': peeled.routes,
            'residual': peeled.residual,
        }
        if bool((torch.triu(P, diagonal=1) == 0).all()):
            out['exact_causal_expected_core_fraction'] = P.diagonal(dim1=-2, dim2=-1).sum(-1) / n
        if V is not None:
            residual_out = peeled.residual @ V
            out['retained_core_output'] = core_out.reshape(*shape, n, V.shape[-1])
            out['retained_nilpotent_output'] = nil_out.reshape(*shape, n, V.shape[-1])
            out['residual_output'] = residual_out
            out['reconstructed_output'] = (out['retained_core_output'] +
                                           out['retained_nilpotent_output'] + residual_out)
            out['max_readout_residual'] = (out['reconstructed_output'] - P @ V).abs().amax()
        return out

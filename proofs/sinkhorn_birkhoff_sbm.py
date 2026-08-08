import math
from dataclasses import dataclass

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, Dataset


@dataclass(frozen=True)
class SBMConfig:
    num_nodes: int = 128
    num_communities: int = 8
    seq_len: int = 64
    num_samples: int = 4096
    p_in: float = 0.25
    p_out: float = 0.02
    restart_prob: float = 0.05
    seed: int = 42


def make_community_assignments(num_nodes: int, num_communities: int) -> torch.Tensor:
    return torch.arange(num_nodes) % num_communities


def make_sbm_adjacency(
    community: torch.Tensor,
    p_in: float,
    p_out: float,
    generator: torch.Generator,
) -> torch.Tensor:
    num_nodes = community.numel()
    same = community[:, None] == community[None, :]
    probs = torch.where(
        same,
        torch.full((num_nodes, num_nodes), p_in),
        torch.full((num_nodes, num_nodes), p_out),
    )
    upper = torch.rand((num_nodes, num_nodes), generator=generator) < probs
    upper = torch.triu(upper, diagonal=1)
    adj = upper | upper.T

    degrees = adj.sum(dim=-1)
    for i in torch.where(degrees == 0)[0].tolist():
        candidates = torch.where((community == community[i]) & (torch.arange(num_nodes) != i))[0]
        if candidates.numel() == 0:
            candidates = torch.tensor([j for j in range(num_nodes) if j != i])
        j = candidates[torch.randint(candidates.numel(), (1,), generator=generator)].item()
        adj[i, j] = True
        adj[j, i] = True

    return adj


def adjacency_to_transition(adj: torch.Tensor) -> torch.Tensor:
    weights = adj.float()
    return weights / weights.sum(dim=-1, keepdim=True).clamp_min(1.0)


class SBMRandomWalkDataset(Dataset):
    def __init__(self, cfg: SBMConfig):
        super().__init__()
        self.cfg = cfg
        self.generator = torch.Generator().manual_seed(cfg.seed)
        self.community = make_community_assignments(cfg.num_nodes, cfg.num_communities)
        self.adj = make_sbm_adjacency(self.community, cfg.p_in, cfg.p_out, self.generator)
        self.transition = adjacency_to_transition(self.adj)
        self.walks = torch.stack([self._sample_walk() for _ in range(cfg.num_samples)], dim=0)

    def _sample_walk(self) -> torch.Tensor:
        walk = torch.empty(self.cfg.seq_len + 1, dtype=torch.long)
        current = torch.randint(0, self.cfg.num_nodes, (1,), generator=self.generator).item()
        walk[0] = current
        for t in range(1, self.cfg.seq_len + 1):
            if torch.rand((), generator=self.generator).item() < self.cfg.restart_prob:
                current = torch.randint(0, self.cfg.num_nodes, (1,), generator=self.generator).item()
            else:
                probs = self.transition[current]
                current = torch.multinomial(probs, 1, True, generator=self.generator).item()
            walk[t] = current
        return walk

    def __len__(self) -> int:
        return self.cfg.num_samples

    def __getitem__(self, idx: int) -> dict[str, torch.Tensor]:
        walk = self.walks[idx]
        input_ids, target_ids = walk[:-1], walk[1:]
        communities = self.community[input_ids]
        community_same = (communities[:, None] == communities[None, :]).float()
        node_adjacency_local = self.adj[input_ids[:, None], input_ids[None, :]].float()
        return {
            "input_ids": input_ids,
            "target_ids": target_ids,
            "communities": communities,
            "community_same": community_same,
            "node_adjacency_local": node_adjacency_local,
        }


def log_sinkhorn(logits: torch.Tensor, n_iters: int = 8) -> torch.Tensor:
    z = logits
    for _ in range(n_iters):
        z = z - torch.logsumexp(z, dim=-1, keepdim=True)
        z = z - torch.logsumexp(z, dim=-2, keepdim=True)
    return z.exp()


def row_normalize_target(target: torch.Tensor, eps: float = 1e-8) -> torch.Tensor:
    return target / (target.sum(dim=-1, keepdim=True) + eps)


def graph_transport_loss(pred_graph: torch.Tensor, target_graph: torch.Tensor) -> torch.Tensor:
    target = row_normalize_target(target_graph)
    pred = pred_graph.clamp_min(1e-8)
    kl = F.kl_div(pred.log(), target, reduction="none")
    return kl.sum(dim=-1).mean()


def edge_auc_approx(pred_graph: torch.Tensor, target_graph: torch.Tensor) -> float:
    scores = pred_graph.detach().flatten()
    labels = target_graph.detach().flatten().bool()
    pos = scores[labels]
    neg = scores[~labels]
    if pos.numel() == 0 or neg.numel() == 0:
        return float("nan")

    if pos.numel() * neg.numel() > 100_000:
        g = torch.Generator(device=scores.device).manual_seed(0)
        pos = pos[torch.randint(pos.numel(), (min(pos.numel(), 512),), generator=g, device=scores.device)]
        neg = neg[torch.randint(neg.numel(), (min(neg.numel(), 512),), generator=g, device=scores.device)]

    comparisons = (pos[:, None] > neg[None, :]).float()
    ties = (pos[:, None] == neg[None, :]).float() * 0.5
    return (comparisons + ties).mean().item()


def dustbin_sinkhorn_diagnostics(attn_ext: torch.Tensor, n_real: int) -> dict[str, float]:
    p_real = attn_ext[:, :, :n_real, :n_real]
    return {
        "ext_row_err": (attn_ext.sum(dim=-1) - 1).abs().mean().item(),
        "ext_col_err": (attn_ext.sum(dim=-2) - 1).abs().mean().item(),
        "real_row_mean": p_real.sum(dim=-1).mean().item(),
        "real_col_mean": p_real.sum(dim=-2).mean().item(),
        "real_row_max": p_real.sum(dim=-1).max().item(),
        "real_col_max": p_real.sum(dim=-2).max().item(),
        "finite": torch.isfinite(attn_ext).all().item(),
    }


class DustbinBirkhoffAttention(nn.Module):
    def __init__(self, d_model: int, n_heads: int, sinkhorn_iters: int = 8, num_dustbins: int = 4):
        super().__init__()
        if d_model % n_heads != 0:
            raise ValueError("d_model must be divisible by n_heads")
        self.d_model = d_model
        self.n_heads = n_heads
        self.d_head = d_model // n_heads
        self.sinkhorn_iters = sinkhorn_iters
        self.num_dustbins = num_dustbins

        self.dustbin_states = nn.Parameter(torch.randn(num_dustbins, d_model) * 0.02)
        self.q_proj = nn.Linear(d_model, d_model, bias=False)
        self.k_proj = nn.Linear(d_model, d_model, bias=False)
        self.v_proj = nn.Linear(d_model, d_model, bias=False)
        self.out_proj = nn.Linear(d_model, d_model, bias=False)

    def split_heads(self, x: torch.Tensor) -> torch.Tensor:
        b, n, _ = x.shape
        return x.view(b, n, self.n_heads, self.d_head).transpose(1, 2)

    def merge_heads(self, x: torch.Tensor) -> torch.Tensor:
        b, h, n, d = x.shape
        return x.transpose(1, 2).contiguous().view(b, n, h * d)

    def forward(self, x: torch.Tensor):
        B, N, _ = x.shape
        dustbins = self.dustbin_states.unsqueeze(0).expand(B, -1, -1)
        x_ext = torch.cat([x, dustbins], dim=1)

        q = self.split_heads(self.q_proj(x_ext))
        k = self.split_heads(self.k_proj(x_ext))
        v = self.split_heads(self.v_proj(x_ext))

        logits = torch.matmul(q, k.transpose(-1, -2)) / math.sqrt(self.d_head)
        attn_ext = log_sinkhorn(logits, self.sinkhorn_iters)

        y_ext = torch.matmul(attn_ext, v)
        y_ext = self.out_proj(self.merge_heads(y_ext))

        return y_ext[:, :N, :], attn_ext[:, :, :N, :N], attn_ext


class LearnedNonnegativeFactorizer(nn.Module):
    def __init__(self, d_model: int, n_heads: int, rank: int, sinkhorn_iters: int = 6, num_dustbins: int = 4):
        super().__init__()
        self.n_heads = n_heads
        self.rank = rank
        self.num_dustbins = num_dustbins
        self.sinkhorn_iters = sinkhorn_iters

        self.graph_dustbin_states = nn.Parameter(torch.randn(num_dustbins, d_model) * 0.02)
        self.w_proj = nn.Linear(d_model, n_heads * rank, bias=False)
        self.h_proj = nn.Linear(d_model, n_heads * rank, bias=False)

    def forward(self, x: torch.Tensor):
        B, N, D = x.shape
        graph_dustbins = self.graph_dustbin_states.unsqueeze(0).expand(B, -1, -1)
        x_graph_ext = torch.cat([x, graph_dustbins], dim=1)
        N_ext = N + self.num_dustbins

        W = F.softplus(self.w_proj(x_graph_ext)).view(B, N_ext, self.n_heads, self.rank).transpose(1, 2)
        H = F.softplus(self.h_proj(x_graph_ext)).view(B, N_ext, self.n_heads, self.rank).transpose(1, 2)

        graph_logits = torch.matmul(W, H.transpose(-1, -2))
        graph_ext = log_sinkhorn((graph_logits + 1e-8).log(), self.sinkhorn_iters)
        graph_real = graph_ext[:, :, :N, :N]
        return graph_real, graph_ext, W, H


class TomographicBirkhoffBlock(nn.Module):
    def __init__(
        self,
        d_model: int,
        n_heads: int,
        n_concepts: int,
        sinkhorn_iters: int = 8,
        num_dustbins: int = 4,
    ):
        super().__init__()
        self.norm = nn.LayerNorm(d_model)
        self.attn = DustbinBirkhoffAttention(
            d_model=d_model,
            n_heads=n_heads,
            sinkhorn_iters=sinkhorn_iters,
            num_dustbins=num_dustbins,
        )
        self.factor = LearnedNonnegativeFactorizer(
            d_model=d_model,
            n_heads=n_heads,
            rank=n_concepts,
            sinkhorn_iters=max(3, sinkhorn_iters // 2),
            num_dustbins=num_dustbins,
        )

    def forward(self, x: torch.Tensor, coupled_grad: bool = False):
        y, p_real, attn_ext = self.attn(self.norm(x))
        x_out = x + y

        a_real, a_ext, w, h = self.factor(x_out)

        target_attn = p_real if coupled_grad else p_real.detach()
        recon_loss = F.mse_loss(a_real, target_attn)

        return {
            "x": x_out,
            "attn_real": p_real,
            "attn_ext": attn_ext,
            "reconstructed_graph": a_real,
            "reconstructed_ext": a_ext,
            "W": w,
            "H": h,
            "recon_loss": recon_loss,
        }


class SBMGraphModel(nn.Module):
    def __init__(
        self,
        cfg: SBMConfig,
        d_model: int = 128,
        num_heads: int = 4,
        graph_rank: int = 8,
        num_dustbins: int = 4,
    ):
        super().__init__()
        self.token_embedding = nn.Embedding(cfg.num_nodes, d_model)
        self.block = TomographicBirkhoffBlock(
            d_model=d_model,
            n_heads=num_heads,
            n_concepts=graph_rank,
            sinkhorn_iters=8,
            num_dustbins=num_dustbins,
        )
        self.output_head = nn.Linear(d_model, cfg.num_nodes)

    def forward(self, input_ids: torch.Tensor, coupled_grad: bool = False):
        out = self.block(self.token_embedding(input_ids), coupled_grad=coupled_grad)
        out["logits"] = self.output_head(out["x"])
        return out


def grad_stats(module: nn.Module) -> dict[str, float]:
    norms = []
    for p in module.parameters():
        if p.requires_grad and p.grad is not None:
            norms.append(p.grad.detach().norm().item())
    if not norms:
        return {"min": 0.0, "mean": 0.0, "max": 0.0}
    t = torch.tensor(norms)
    return {"min": t.min().item(), "mean": t.mean().item(), "max": t.max().item()}


def smoke_train() -> None:
    torch.manual_seed(0)

    cfg = SBMConfig()
    dataset = SBMRandomWalkDataset(cfg)
    loader = DataLoader(dataset, batch_size=16, shuffle=True, num_workers=0)

    model = SBMGraphModel(
        cfg=cfg,
        d_model=128,
        num_heads=4,
        graph_rank=cfg.num_communities,
        num_dustbins=4,
    )
    optimizer = torch.optim.AdamW(model.parameters(), lr=1e-3)

    print(f"{'step':>4} | {'loss':>8} | {'task':>8} | {'graph':>8} | {'recon':>8} | {'auc':>5} | {'ext err':>15} | {'real mass mean/max':>19}")
    print("-" * 100)

    model.train()
    for step, batch in enumerate(loader):
        optimizer.zero_grad(set_to_none=True)

        out = model(batch["input_ids"], coupled_grad=False)

        task_loss = F.cross_entropy(
            out["logits"].reshape(-1, cfg.num_nodes),
            batch["target_ids"].reshape(-1),
        )
        graph_loss = graph_transport_loss(out["reconstructed_graph"], batch["community_same"])
        loss = task_loss + graph_loss + 0.1 * out["recon_loss"]
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        optimizer.step()

        if step % 10 == 0:
            diag = dustbin_sinkhorn_diagnostics(out["attn_ext"], cfg.seq_len)
            auc = edge_auc_approx(out["reconstructed_graph"], batch["community_same"])
            print(
                f"{step:4d} | {loss.item():8.4f} | {task_loss.item():8.4f} | {graph_loss.item():8.4f} | "
                f"{out['recon_loss'].item():8.4f} | {auc:5.3f} | "
                f"{diag['ext_row_err']:.1e}/{diag['ext_col_err']:.1e} | "
                f"{diag['real_row_mean']:.3f}/{diag['real_row_max']:.3f}"
            )

        if step >= 150:
            break

    print("-" * 100)
    print("grad stats:", grad_stats(model))
    print("smoke_train complete")


if __name__ == "__main__":
    smoke_train()

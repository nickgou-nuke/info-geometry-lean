import os
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parent
FIG_DIR = ROOT / "figures"
LEAN_ROOT = ROOT.parent / "lean" / "InfoGeometry"


def _style() -> None:
    # Use an available Matplotlib style without hard-failing.
    preferred = [
        "seaborn-v0_8-whitegrid",
        "seaborn-whitegrid",
        "ggplot",
    ]
    for s in preferred:
        try:
            plt.style.use(s)
            return
        except OSError:
            continue


def _save(fig: plt.Figure, name: str) -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    out = FIG_DIR / name
    fig.tight_layout()
    fig.savefig(out, dpi=300)
    plt.close(fig)
    print(f"[ok] {out}")


def gen_kl_divergence() -> None:
    p = 0.35
    q = np.linspace(0.01, 0.99, 500)
    kl = p * np.log(p / q) + (1 - p) * np.log((1 - p) / (1 - q))

    fig, ax = plt.subplots(figsize=(8.0, 4.8))
    ax.plot(q, kl, color="#1f77b4", linewidth=2.5, label=r"$D_{KL}(P\Vert Q)$")
    ax.axvline(x=p, color="#d62728", linestyle="--", linewidth=1.8, label=rf"$p={p:.2f}$")
    ax.set_title("KL Divergence Landscape (Bernoulli Family)")
    ax.set_xlabel("q")
    ax.set_ylabel(r"$D_{KL}(P\Vert Q)$")
    ax.set_xlim(0, 1)
    ax.set_ylim(bottom=0)
    ax.legend(frameon=True)
    _save(fig, "kl_divergence.png")


def gen_fisher_information() -> None:
    theta = np.linspace(0.01, 0.99, 500)
    fisher = 1 / (theta * (1 - theta))

    fig, ax = plt.subplots(figsize=(8.0, 4.8))
    ax.plot(theta, fisher, color="#2ca02c", linewidth=2.5)
    ax.set_title("Fisher Information for Bernoulli")
    ax.set_xlabel(r"$\theta$")
    ax.set_ylabel(r"$I(\theta)=1/(\theta(1-\theta))$")
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 60)
    _save(fig, "fisher_info.png")


def gen_entropy_manifold() -> None:
    mu = np.linspace(-3.0, 3.0, 240)
    sigma = np.linspace(0.2, 2.5, 240)
    m_grid, s_grid = np.meshgrid(mu, sigma)
    entropy = 0.5 * np.log(2 * np.pi * np.e * (s_grid**2))

    fig, ax = plt.subplots(figsize=(8.0, 4.8))
    c = ax.contourf(m_grid, s_grid, entropy, levels=24, cmap="viridis")
    fig.colorbar(c, ax=ax, label="Differential entropy")
    ax.set_title(r"Entropy Surface on Gaussian Manifold $N(\mu,\sigma^2)$")
    ax.set_xlabel(r"$\mu$")
    ax.set_ylabel(r"$\sigma$")
    _save(fig, "entropy_manifold.png")


def _count_lean_files(folder: Path) -> int:
    if not folder.exists():
        return 0
    return sum(1 for p in folder.rglob("*.lean") if p.is_file())


def gen_module_coverage() -> None:
    buckets = [
        "Core",
        "Convex",
        "Geometry",
        "KL",
        "ExponentialFamily",
        "Thermo",
        "Potential",
        "Clifford",
        "Krein",
        "MaxEnt",
        "Research",
        "LLM",
    ]
    counts = [_count_lean_files(LEAN_ROOT / b) for b in buckets]

    fig, ax = plt.subplots(figsize=(8.0, 5.0))
    y = np.arange(len(buckets))
    bars = ax.barh(y, counts, color="#4C78A8")
    ax.set_yticks(y)
    ax.set_yticklabels(buckets)
    ax.set_xlabel("Lean files")
    ax.set_title("Library Breadth by Module Family")
    ax.invert_yaxis()

    for bar, c in zip(bars, counts):
        ax.text(bar.get_width() + 0.3, bar.get_y() + bar.get_height() / 2, str(c), va="center")

    _save(fig, "module_coverage.png")


def gen_bridge_map() -> None:
    domains = [
        "Stats",
        "Convex",
        "Thermo",
        "Geometry",
        "Spectral",
        "LLM",
    ]
    # Symmetric "bridge density" proxy for presentation purposes.
    mat = np.array(
        [
            [0, 8, 7, 6, 4, 5],
            [8, 0, 9, 8, 5, 6],
            [7, 9, 0, 6, 7, 8],
            [6, 8, 6, 0, 7, 4],
            [4, 5, 7, 7, 0, 6],
            [5, 6, 8, 4, 6, 0],
        ],
        dtype=float,
    )

    fig, ax = plt.subplots(figsize=(7.2, 6.2))
    im = ax.imshow(mat, cmap="magma", vmin=0, vmax=9)
    fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04, label="Bridge density")
    ax.set_xticks(np.arange(len(domains)))
    ax.set_yticks(np.arange(len(domains)))
    ax.set_xticklabels(domains)
    ax.set_yticklabels(domains)
    ax.set_title("Cross-Domain Bridge Map")

    for i in range(mat.shape[0]):
        for j in range(mat.shape[1]):
            if i != j:
                ax.text(j, i, int(mat[i, j]), ha="center", va="center", color="white", fontsize=9)

    _save(fig, "bridge_map.png")


def gen_transformer_pipeline() -> None:
    fig, ax = plt.subplots(figsize=(10.0, 4.8))
    ax.axis("off")

    def box(x, y, w, h, text, color="#4C78A8"):
        rect = plt.Rectangle((x, y), w, h, facecolor=color, alpha=0.18, edgecolor=color, linewidth=2)
        ax.add_patch(rect)
        ax.text(x + w / 2, y + h / 2, text, ha="center", va="center", fontsize=10)

    # Top-level flow.
    box(0.02, 0.63, 0.14, 0.24, "Input\nQuery State")
    box(0.20, 0.63, 0.16, 0.24, "Positional\nEncoding", color="#F58518")
    box(0.40, 0.58, 0.38, 0.34, "MaskedTransformerBlock", color="#54A24B")
    box(0.82, 0.63, 0.15, 0.24, "Output\nState")

    # Internal stack.
    box(0.43, 0.80, 0.32, 0.08, "Multi-Head Attention")
    box(0.43, 0.70, 0.32, 0.08, "Residual + Norm1")
    box(0.43, 0.60, 0.32, 0.08, "MLP")
    box(0.43, 0.50, 0.32, 0.08, "Residual + Norm2")

    def arrow(x1, y1, x2, y2):
        ax.annotate("", xy=(x2, y2), xytext=(x1, y1), arrowprops=dict(arrowstyle="->", linewidth=1.8))

    arrow(0.16, 0.75, 0.20, 0.75)
    arrow(0.36, 0.75, 0.40, 0.75)
    arrow(0.78, 0.75, 0.82, 0.75)
    arrow(0.59, 0.80, 0.59, 0.78)
    arrow(0.59, 0.70, 0.59, 0.68)
    arrow(0.59, 0.60, 0.59, 0.58)

    ax.set_title("LLM Stack in the Library: Positional + Causal-Masked Transformer Block", fontsize=12, pad=14)
    _save(fig, "transformer_pipeline.png")


def gen_ricci_bridge() -> None:
    fig, ax = plt.subplots(figsize=(10.0, 4.6))
    ax.axis("off")

    def node(x, y, w, h, text, color):
        rect = plt.Rectangle((x, y), w, h, facecolor=color, alpha=0.18, edgecolor=color, linewidth=2)
        ax.add_patch(rect)
        ax.text(x + w / 2, y + h / 2, text, ha="center", va="center", fontsize=10)

    node(0.03, 0.58, 0.20, 0.28, "HessianGeometry\nmetricOp", "#4C78A8")
    node(0.29, 0.58, 0.20, 0.28, "ricciFromMetricOp\nStrongRicciFromHessian", "#54A24B")
    node(0.55, 0.58, 0.20, 0.28, "Einstein-Kahler\nCompatibility", "#F58518")
    node(0.79, 0.58, 0.18, 0.28, "Ricci Flow\nbeta", "#E45756")

    node(0.24, 0.14, 0.22, 0.28, "Monge-Ampere\nDensity", "#72B7B2")
    node(0.52, 0.14, 0.22, 0.28, "Heat Kernel /\nSpectral Bridge", "#B279A2")

    def arrow(x1, y1, x2, y2):
        ax.annotate("", xy=(x2, y2), xytext=(x1, y1), arrowprops=dict(arrowstyle="->", linewidth=1.8))

    arrow(0.23, 0.72, 0.29, 0.72)
    arrow(0.49, 0.72, 0.55, 0.72)
    arrow(0.75, 0.72, 0.79, 0.72)
    arrow(0.39, 0.58, 0.35, 0.42)
    arrow(0.65, 0.58, 0.63, 0.42)
    arrow(0.46, 0.28, 0.52, 0.28)

    ax.set_title("Geometric PDE Layer: Hessian -> Ricci -> Einstein-Kahler -> Monge-Ampere", fontsize=12, pad=12)
    _save(fig, "ricci_bridge.png")


def main() -> None:
    _style()
    print("[info] generating presentation figures...")
    gen_kl_divergence()
    gen_fisher_information()
    gen_entropy_manifold()
    gen_module_coverage()
    gen_bridge_map()
    gen_transformer_pipeline()
    gen_ricci_bridge()
    print("[info] done")


if __name__ == "__main__":
    main()

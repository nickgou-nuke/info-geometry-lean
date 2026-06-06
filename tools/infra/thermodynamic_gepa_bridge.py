#!/usr/bin/env python3
"""Thermodynamic GEPA Bridge — connects the phase transition theorem to mutation rate control.

Reads the empirical strategy population from the GEPA evolver, computes
stiffness (A) and fluctuation (B) matrices, checks the phase transition
condition, and adjusts the mutation rate accordingly.

Usage:
    python3 tools/infra/thermodynamic_gepa_bridge.py [--population PATH] [--rate FLOAT]
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
EVAL_CACHE = REPO / "quarantine" / "hermes_skills" / "evolved" / ".eval_cache.jsonl"


def load_population(cache_path: Path = EVAL_CACHE) -> list[dict]:
    """Load the GEPA strategy population from the eval cache."""
    population = []
    if not cache_path.exists():
        print(f"Warning: {cache_path} not found. Using synthetic data.", file=sys.stderr)
        return _synthetic_population()

    with open(cache_path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                entry = json.loads(line)
            except json.JSONDecodeError:
                continue
            # Parse fitness (1.0 = compiled, 0.0 = sorry present)
            fitness = entry.get("score", 0.0)
            if isinstance(fitness, (int, float)):
                population.append({
                    "fitness": float(fitness),
                    "gradient": _compute_gradient(entry),
                })
    return population


def _synthetic_population() -> list[dict]:
    """Generate synthetic population for testing."""
    import random
    pop = []
    for i in range(20):
        fitness = random.uniform(0.0, 1.0)
        grad = [random.gauss(0, 0.1) for _ in range(5)]
        pop.append({"fitness": fitness, "gradient": grad})
    return pop


def _compute_gradient(entry: dict) -> list[float]:
    """Compute a gradient vector from the eval entry metadata."""
    # In production, this would parse the actual tactic/strategy features.
    # For now, use available metadata as a proxy.
    grad = []
    for key in ["term_node_count", "unfolded_local_wrapper_count", "contains_sorry"]:
        val = entry.get(key, 0)
        if isinstance(val, bool):
            val = 1.0 if val else 0.0
        grad.append(float(val) if val else 0.0)
    # Pad or truncate to 5 dimensions
    while len(grad) < 5:
        grad.append(0.0)
    return grad[:5]


def compute_stiffness(population: list[dict], k: int = 5) -> list[list[float]]:
    """Compute stiffness matrix A."""
    n = len(population)
    if n == 0:
        return [[0.0] * k for _ in range(k)]

    # Mean gradient
    g_avg = [0.0] * k
    for s in population:
        for a in range(k):
            g_avg[a] += s["gradient"][a]
    g_avg = [g / n for g in g_avg]

    # A_ab = g_avg[a] * g_avg[b]
    A = [[g_avg[a] * g_avg[b] for b in range(k)] for a in range(k)]
    return A


def compute_fluctuation(population: list[dict], eps: float, k: int = 5) -> list[list[float]]:
    """Compute fluctuation pressure matrix B."""
    n = len(population)
    if n == 0 or eps == 0.0:
        return [[0.0] * k for _ in range(k)]

    g_avg = [0.0] * k
    for s in population:
        for a in range(k):
            g_avg[a] += s["gradient"][a]
    g_avg = [g / n for g in g_avg]

    B = [[0.0] * k for _ in range(k)]
    for a in range(k):
        for b in range(k):
            cov = sum(
                (s["gradient"][a] - g_avg[a]) * (s["gradient"][b] - g_avg[b])
                for s in population
            ) / n
            B[a][b] = (1.0 / eps) * cov if eps != 0 else 0.0
    return B


def check_stability(A: list[list[float]], B: list[list[float]]) -> tuple[bool, float]:
    """Check if the system is stable (A - B is positive-definite).

    Returns (is_stable, max_eigenvalue_ratio).
    """
    k = len(A)
    # H = A - B
    H = [[A[i][j] - B[i][j] for j in range(k)] for i in range(k)]

    # Check positive-definiteness via leading principal minors (Sylvester's criterion)
    for m in range(1, k + 1):
        det = _leading_minor(H, m)
        if det <= 0:
            return False, det

    # Compute max eigenvalue ratio (spectral radius of B relative to A)
    # Simple heuristic: largest entry ratio
    max_ratio = 0.0
    for i in range(k):
        for j in range(k):
            if abs(A[i][j]) > 1e-10:
                ratio = abs(B[i][j] / A[i][j])
                max_ratio = max(max_ratio, ratio)

    return True, max_ratio


def _leading_minor(M: list[list[float]], m: int) -> float:
    """Compute the leading principal minor of order m."""
    if m == 0:
        return 1.0
    sub = [[M[i][j] for j in range(m)] for i in range(m)]
    return _det(sub)


def _det(M: list[list[float]]) -> float:
    """Compute determinant (only small matrices)."""
    n = len(M)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    # For larger, use recursion (fine for k <= 5)
    det = 0.0
    for j in range(n):
        sub = [[M[i][col] for col in range(n) if col != j] for i in range(1, n)]
        sign = 1.0 if j % 2 == 0 else -1.0
        det += sign * M[0][j] * _det(sub)
    return det


def critical_temperature(population: list[dict]) -> float:
    """Compute the critical temperature (maximum stable mutation rate)."""
    k = 5
    n = len(population)
    if n < 2:
        return 1.0

    # Variance-to-mean ratio heuristic
    total_variance = 0.0
    g_avg = [0.0] * k
    for s in population:
        for a in range(k):
            g_avg[a] += s["gradient"][a]
    g_avg = [g / n for g in g_avg]

    for s in population:
        for a in range(k):
            total_variance += (s["gradient"][a] - g_avg[a]) ** 2

    mean_energy = sum(1.0 - s["fitness"] for s in population) / n

    if total_variance == 0.0:
        return 1.0
    return mean_energy / total_variance


def recommend_mutation_rate(population: list[dict], recent_success_rate: float) -> float:
    """Recommend mutation rate based on thermodynamic stability."""
    eps_crit = critical_temperature(population)

    if recent_success_rate < 0.1:
        return eps_crit * 2.0   # heat up
    elif recent_success_rate > 0.4:
        return eps_crit / 2.0   # cool down
    else:
        return eps_crit


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Thermodynamic GEPA Bridge")
    parser.add_argument("--population", type=str, default=str(EVAL_CACHE))
    parser.add_argument("--rate", type=float, default=None,
                        help="Current mutation rate (if omitted, compute recommended)")
    parser.add_argument("--success-rate", type=float, default=0.2,
                        help="Recent success rate (0-1)")
    args = parser.parse_args()

    population = load_population(Path(args.population))

    if not population:
        print("No population data. Using synthetic data.")
        population = _synthetic_population()

    eps = args.rate if args.rate is not None else 0.1

    A = compute_stiffness(population)
    B = compute_fluctuation(population, eps)
    stable, ratio = check_stability(A, B)
    eps_crit = critical_temperature(population)
    recommended = recommend_mutation_rate(population, args.success_rate)

    print(f"=== Thermodynamic GEPA Regulation ===")
    print(f"Population size: {len(population)}")
    print(f"  Current ε:     {eps:.4f}")
    print(f"  Critical ε:    {eps_crit:.4f}")
    print(f"  Recommended ε: {recommended:.4f}")
    print(f"  Stable:        {stable}")
    print(f"  B/A ratio:     {ratio:.4f}")
    print(f"  Success rate:  {args.success_rate:.2f}")

    if not stable:
        print(f"\n⚠ WARNING: Phase transition detected! Fluctuations exceed stiffness.")
        print(f"  Reduce mutation rate to at most {eps_crit:.4f} to restore stability.")
    elif eps > eps_crit:
        print(f"\n⚠ Current ε exceeds critical ε. Reduce to {eps_crit:.4f}.")
    else:
        print(f"\n✓ System is stable. Current mutation rate is within bounds.")


if __name__ == "__main__":
    main()

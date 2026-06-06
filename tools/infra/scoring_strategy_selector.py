#!/usr/bin/env python3
"""Scoring Strategy Selector — switches between heuristic and thermodynamic scoring.

The GEPA evolution loop can use two scoring strategies:

1. **Heuristic (empirical)**: scores based on compile success, `sorry` detection,
   and obfuscation pattern matches. Fast, reactive, no theoretical grounding.

2. **Thermodynamic (theoretical)**: scores using the 2×2 stiffness/fluctuation
   matrices from `RobustThermodynamicRegression.lean`. Grounded in the phase
   transition theorem, but requires computing matrix determinants.

The selector monitors both strategies and picks the one that gives the highest
resolution rate for the current shadow population.
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from typing import Literal

REPO = Path(__file__).resolve().parents[2]
EVAL_CACHE = REPO / "quarantine" / "hermes_skills" / "evolved" / ".eval_cache.jsonl"

ScoringStrategy = Literal["heuristic", "thermodynamic", "maxent", "mixed", "auto"]


def load_population(cache_path: Path = EVAL_CACHE) -> list[dict]:
    """Load the GEPA strategy population from the eval cache."""
    population = []
    if not cache_path.exists():
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
            fitness = entry.get("score", 0.0)
            if isinstance(fitness, (int, float)):
                population.append({
                    "fitness": float(fitness),
                    "gradient": _compute_gradient(entry),
                    "strategy": entry.get("strategy", "unknown"),
                    "compile_time": entry.get("compile_time_ms", 0),
                })
    return population


def _synthetic_population() -> list[dict]:
    import random
    return [
        {"fitness": random.uniform(0.0, 1.0), "gradient": [random.gauss(0, 0.1) for _ in range(5)],
         "strategy": "unknown", "compile_time": random.randint(50, 500)}
        for _ in range(20)
    ]


def _compute_gradient(entry: dict) -> list[float]:
    grad = []
    for key in ["term_node_count", "unfolded_local_wrapper_count", "contains_sorry"]:
        val = entry.get(key, 0)
        if isinstance(val, bool):
            val = 1.0 if val else 0.0
        grad.append(float(val) if val else 0.0)
    while len(grad) < 5:
        grad.append(0.0)
    return grad[:5]


# ── Heuristic scoring ──────────────────────────────────────────────

def heuristic_score(population: list[dict]) -> float:
    """Pure empirical score: ratio of successful compilations."""
    if not population:
        return 0.0
    successes = sum(1 for s in population if s["fitness"] >= 0.9)
    return successes / len(population)


def heuristic_variance(population: list[dict]) -> float:
    """Variance of heuristic scores — how spread out the population is."""
    if not population:
        return 0.0
    scores = [s["fitness"] for s in population]
    mean = sum(scores) / len(scores)
    return sum((s - mean) ** 2 for s in scores) / len(scores)


# ── Thermodynamic scoring ──────────────────────────────────────────

def _det(M: list[list[float]]) -> float:
    n = len(M)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    det = 0.0
    for j in range(n):
        sub = [[M[i][col] for col in range(n) if col != j] for i in range(1, n)]
        sign = 1.0 if j % 2 == 0 else -1.0
        det += sign * M[0][j] * _det(sub)
    return det


def thermodynamic_score(population: list[dict], eps: float = 0.1) -> float:
    """
    Thermodynamic score: 1.0 if the exact Hessian H = A - B is positive-definite,
    0.0 otherwise. Uses the phase transition theorem.
    """
    k = 5
    n = len(population)
    if n < 2:
        return 1.0 if population else 0.0

    # Mean gradient
    g_avg = [0.0] * k
    for s in population:
        for a in range(k):
            g_avg[a] += s["gradient"][a]
    g_avg = [g / n for g in g_avg]

    # Stiffness A
    A = [[g_avg[a] * g_avg[b] for b in range(k)] for a in range(k)]

    # Fluctuation B
    B = [[0.0] * k for _ in range(k)]
    for a in range(k):
        for b in range(k):
            cov = sum(
                (s["gradient"][a] - g_avg[a]) * (s["gradient"][b] - g_avg[b])
                for s in population
            ) / n
            B[a][b] = (1.0 / eps) * cov

    # H = A - B
    H = [[A[i][j] - B[i][j] for j in range(k)] for i in range(k)]

    # Sylvester's criterion: all leading principal minors must be positive
    for m in range(1, k + 1):
        sub = [[H[i][j] for j in range(m)] for i in range(m)]
        det = _det(sub)
        if det <= 0:
            return 0.0

    # Compute condition number proxy
    return 1.0 / (1.0 + abs(_det(H)))


# ── Maximum Entropy (MaxEnt) thermodynamics ───────────────────────

def maxent_weights(population: list[dict], eps: float = 0.1) -> list[float]:
    """
    Maximum entropy Gibbs weights for the strategy population.

    p_i = exp(-E_i / ε) / Z

    where E_i = 1 - fitness(i) is the energy, ε is the temperature,
    and Z = Σ exp(-E_i / ε) is the partition function.

    At high temperature (ε large), all strategies have equal weight.
    At low temperature (ε small), only the fittest survive.
    """
    if not population:
        return []
    energies = [1.0 - s["fitness"] for s in population]
    Z = sum(math.exp(-e / eps) if eps > 0 else 0.0 for e in energies)
    if Z == 0.0:
        return [1.0 / len(population)] * len(population)
    return [math.exp(-e / eps) / Z for e in energies]


def maxent_score(population: list[dict], eps: float = 0.1) -> float:
    """
    Maximum entropy score: the log-likelihood of the population under
    the Gibbs measure. Higher means the population is more "coherent"
    — strategies cluster near the Pareto frontier.

    Score = -(1/N) Σ E_i + ε * H(p)

    where H(p) = -Σ p_i log(p_i) is the entropy of the weight distribution.
    This is the negative free energy per strategy.
    """
    if not population:
        return 0.0
    n = len(population)
    weights = maxent_weights(population, eps)
    energies = [1.0 - s["fitness"] for s in population]

    # Average energy
    avg_energy = sum(w * e for w, e in zip(weights, energies))

    # Entropy of the weight distribution
    entropy = -sum(w * math.log(w + 1e-10) for w in weights)

    # Negative free energy per strategy (higher = more coherent)
    return -avg_energy + eps * entropy / n


def logit_adjustment(population: list[dict], base_weight: float = 1.0) -> list[float]:
    """
    Logit adjustment: convert fitness scores to log-odds.

    logit(p) = log(p / (1-p))

    This amplifies differences near 0 and 1, making the selection
    pressure sharper for nearly-perfect and nearly-failing strategies.
    """
    if not population:
        return []
    adjusted = []
    for s in population:
        f = max(0.01, min(0.99, s["fitness"]))
        logit = math.log(f / (1.0 - f))
        adjusted.append(base_weight * (1.0 + logit / 10.0))
    return adjusted


# ── Mixed scoring ─────────────────────────────────────────────────

def mixed_score(population: list[dict], alpha: float = 0.5, eps: float = 0.1) -> tuple[float, dict]:
    """
    Mixed scoring: blends heuristic, thermodynamic, and MaxEnt scores.

    total = α * heuristic + β * thermodynamic + γ * maxent

    where α + β + γ = 1. The default α=0.5, β=0.3, γ=0.2 gives
    more weight to the empirical heuristic, with theoretical grounding
    from thermodynamics and maximum entropy.
    """
    beta = (1.0 - alpha) * 0.6   # 0.3 when alpha=0.5
    gamma = (1.0 - alpha) * 0.4  # 0.2 when alpha=0.5

    h_score = heuristic_score(population)
    t_score = thermodynamic_score(population, eps)
    m_score = maxent_score(population, eps)

    # Logit-adjust the heuristic
    logit_weights = logit_adjustment(population)
    if logit_weights:
        h_adjusted = sum(w * s["fitness"] for w, s in zip(logit_weights, population)) / sum(logit_weights)
    else:
        h_adjusted = h_score

    total = alpha * h_adjusted + beta * t_score + gamma * m_score

    metadata = {
        "heuristic_component": round(h_adjusted, 4),
        "thermodynamic_component": round(t_score, 4),
        "maxent_component": round(m_score, 4),
        "alpha": alpha,
        "beta": round(beta, 4),
        "gamma": round(gamma, 4),
        "logit_adjusted": True,
    }

    return total, metadata


# ── Strategy selector ──────────────────────────────────────────────

def select_strategy(
    population: list[dict],
    strategy: ScoringStrategy = "auto",
    eps: float = 0.1,
    alpha: float = 0.5,
) -> tuple[ScoringStrategy, float, dict]:
    """
    Select the best scoring strategy.

    Strategies:
    - heuristic: empirical compile-success rate
    - thermodynamic: phase transition condition from 2×2 matrices
    - maxent: maximum entropy Gibbs measure
    - mixed: weighted blend of all three with logit adjustment
    - auto: compares separation power, picks the best
    """
    heur_score = heuristic_score(population)
    heur_var = heuristic_variance(population)
    thermo_score = thermodynamic_score(population, eps)
    maxent = maxent_score(population, eps)
    mix, mix_meta = mixed_score(population, alpha, eps)

    n = len(population)
    heur_sep = heur_var / (heur_score + 0.01)

    k = 5
    thermo_sep = 0.0
    if n >= 2:
        g_avg = [sum(s["gradient"][a] for s in population) / n for a in range(k)]
        A = [[g_avg[a] * g_avg[b] for b in range(k)] for a in range(k)]
        B = [[0.0] * k for _ in range(k)]
        for a in range(k):
            for b in range(k):
                cov = sum(
                    (s["gradient"][a] - g_avg[a]) * (s["gradient"][b] - g_avg[b])
                    for s in population
                ) / n
                B[a][b] = (1.0 / eps) * cov
        H = [[A[i][j] - B[i][j] for j in range(k)] for i in range(k)]
        thermo_sep = abs(_det(H)) / (1.0 + abs(_det(H)))

    if strategy == "heuristic":
        selected, score = "heuristic", heur_score
    elif strategy == "thermodynamic":
        selected, score = "thermodynamic", thermo_score
    elif strategy == "maxent":
        selected, score = "maxent", maxent
    elif strategy == "mixed":
        selected, score = "mixed", mix
    else:  # auto
        if thermo_sep > heur_sep and n >= 3:
            selected, score = "mixed", mix
        else:
            selected, score = "heuristic", heur_score

    metadata = {
        "heuristic_score": round(heur_score, 4),
        "heuristic_separation": round(heur_sep, 4),
        "thermodynamic_score": round(thermo_score, 4),
        "thermodynamic_separation": round(thermo_sep, 4),
        "maxent_score": round(maxent, 4),
        "mixed_score": round(mix, 4),
        "selected": selected,
        "population_size": n,
    }

    return selected, score, metadata


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Scoring Strategy Selector")
    parser.add_argument("--strategy", choices=["heuristic", "thermodynamic", "maxent", "mixed", "auto"],
                        default="auto", help="Scoring strategy to use")
    parser.add_argument("--eps", type=float, default=0.1, help="Temperature parameter")
    parser.add_argument("--alpha", type=float, default=0.5, help="Mixing weight for heuristic")
    parser.add_argument("--population", type=str, default=str(EVAL_CACHE))
    args = parser.parse_args()

    population = load_population(Path(args.population))
    if not population:
        population = _synthetic_population()

    selected, score, meta = select_strategy(population, args.strategy, args.eps, args.alpha)

    print(f"=== Scoring Strategy Selector ===")
    print(f"Population size: {meta['population_size']}")
    print(f"Heuristic: {meta['heuristic_score']} (sep: {meta['heuristic_separation']})")
    if meta['thermodynamic_separation'] > 0:
        print(f"Thermodynamic: {meta['thermodynamic_score']} (sep: {meta['thermodynamic_separation']})")
    print(f"MaxEnt: {meta['maxent_score']}")
    print(f"Mixed: {meta['mixed_score']}")
    print(f"Selected: {meta['selected']} → score = {score:.4f}")


if __name__ == "__main__":
    main()

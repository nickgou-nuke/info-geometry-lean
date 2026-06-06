#!/usr/bin/env python3
"""Finite thermodynamic scoring helpers for GEPA-style proof search.

The helpers in this module implement a small Gibbs-style reweighting over a
finite set of observed task outcomes.  They are deliberately conservative:

- the energy is a bounded, observable proxy for search cost;
- the temperature is fitted from the observed spread and success rate;
- the returned score stays in [0, 1] so existing callers can use it as a
  selection metric.

This is the runtime counterpart to the repo's MaxEnt / thermodynamic surfaces.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import exp, log, sqrt
from typing import Any, Iterable


def _clamp(value: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, value))


DEFAULT_HEURISTIC_WEIGHT = 0.25


def outcome_energy(
    outcome: dict[str, Any],
    *,
    cost_budget_ms: float = 120_000.0,
) -> float:
    """Map a single task outcome to a nonnegative energy.

    Lower is better.  Successful, fast, single-attempt tasks sit near zero;
    failed or expensive tasks get higher energy.
    """
    succeeded = outcome.get("status") == "completed" or bool(outcome.get("succeeded", False))
    attempts = max(1.0, float(outcome.get("attempts", 1.0) or 1.0))
    cost_ms = max(
        0.0,
        float(outcome.get("metabolic_cost_ms", outcome.get("elapsed_ms", 0.0)) or 0.0),
    )

    failure_penalty = 0.0 if succeeded else 1.0
    attempt_penalty = max(0.0, (attempts - 1.0) / attempts)
    cost_penalty = min(1.0, cost_ms / max(1.0, cost_budget_ms))

    return failure_penalty + 0.5 * attempt_penalty + 0.5 * cost_penalty


@dataclass(frozen=True)
class ThermodynamicScore:
    """Finite Gibbs-style summary of a sample set."""

    fitness: float
    legacy_fitness: float
    thermodynamic_fitness: float
    temperature: float
    partition_function: float
    free_energy: float
    energy_mean: float
    energy_variance: float
    entropy: float
    expected_energy: float
    expected_success: float
    success_rate: float
    energies: tuple[float, ...]
    weights: tuple[float, ...]


def fit_temperature(
    energies: Iterable[float],
    success_rate: float,
    *,
    floor: float = 0.15,
    ceiling: float = 5.0,
) -> float:
    """Fit an effective temperature from the observed energy spread."""
    values = list(energies)
    if not values:
        return 1.0

    mean = sum(values) / len(values)
    variance = sum((x - mean) ** 2 for x in values) / len(values)
    spread = sqrt(max(0.0, variance))

    raw = 0.25 + spread + (1.0 - success_rate) + 0.25 * mean
    return _clamp(raw, floor, ceiling)


def score_outcomes(
    outcomes: list[dict[str, Any]],
    *,
    cost_budget_ms: float = 120_000.0,
    heuristic_weight: float = DEFAULT_HEURISTIC_WEIGHT,
) -> ThermodynamicScore:
    """Compute a finite Gibbs score for a list of outcomes."""
    if not outcomes:
        return ThermodynamicScore(
            fitness=0.0,
            legacy_fitness=0.0,
            thermodynamic_fitness=0.0,
            temperature=1.0,
            partition_function=0.0,
            free_energy=0.0,
            energy_mean=0.0,
            energy_variance=0.0,
            entropy=0.0,
            expected_energy=0.0,
            expected_success=0.0,
            success_rate=0.0,
            energies=(),
            weights=(),
        )

    energies = [outcome_energy(outcome, cost_budget_ms=cost_budget_ms) for outcome in outcomes]
    success_flags = [
        1.0 if (outcome.get("status") == "completed" or bool(outcome.get("succeeded", False))) else 0.0
        for outcome in outcomes
    ]
    success_rate = sum(success_flags) / len(success_flags)
    temperature = fit_temperature(energies, success_rate)

    unnormalized = [exp(-energy / temperature) for energy in energies]
    partition_function = sum(unnormalized)
    if partition_function <= 0.0:
        # Numerically this should not happen, but keep the contract total.
        partition_function = 1.0

    weights = [weight / partition_function for weight in unnormalized]
    expected_energy = sum(weight * energy for weight, energy in zip(weights, energies))
    expected_success = sum(weight * success for weight, success in zip(weights, success_flags))
    energy_mean = sum(energies) / len(energies)
    energy_variance = sum((energy - energy_mean) ** 2 for energy in energies) / len(energies)
    entropy = -sum(weight * log(weight) for weight in weights if weight > 0.0)
    free_energy = -temperature * log(partition_function)
    heuristic_weight = _clamp(heuristic_weight, 0.0, 1.0)
    thermo_weight = 1.0 - heuristic_weight
    mixed_fitness = thermo_weight * expected_success + heuristic_weight * success_rate

    return ThermodynamicScore(
        fitness=max(0.0, min(1.0, mixed_fitness)),
        legacy_fitness=success_rate,
        thermodynamic_fitness=max(0.0, min(1.0, expected_success)),
        temperature=temperature,
        partition_function=partition_function,
        free_energy=free_energy,
        energy_mean=energy_mean,
        energy_variance=energy_variance,
        entropy=entropy,
        expected_energy=expected_energy,
        expected_success=expected_success,
        success_rate=success_rate,
        energies=tuple(energies),
        weights=tuple(weights),
    )

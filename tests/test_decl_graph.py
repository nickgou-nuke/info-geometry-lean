"""Tests for tools/infra/decl_graph.py — declaration graph helper functions."""
from __future__ import annotations

from collections import Counter
from pathlib import Path

import pytest

from tools.infra.decl_graph import (
    dominant_category,
    dominant_pressure,
    normalize_repo_relative,
    primary_action,
    replaceable_surface_mass,
    support_pressure,
)

REPO_ROOT = Path(__file__).resolve().parents[1]


# ---------------------------------------------------------------------------
# normalize_repo_relative
# ---------------------------------------------------------------------------

def test_normalize_repo_relative_absolute_path() -> None:
    root = REPO_ROOT
    abs_path = str(root / "lean" / "InfoGeometry" / "Canonical.lean")
    result = normalize_repo_relative(root, abs_path)
    assert result == "lean/InfoGeometry/Canonical.lean"


def test_normalize_repo_relative_relative_path() -> None:
    root = REPO_ROOT
    result = normalize_repo_relative(root, "lean/InfoGeometry/Canonical.lean")
    assert result == "lean/InfoGeometry/Canonical.lean"


def test_normalize_repo_relative_none_returns_empty() -> None:
    result = normalize_repo_relative(REPO_ROOT, None)
    assert result == ""


def test_normalize_repo_relative_empty_string() -> None:
    result = normalize_repo_relative(REPO_ROOT, "")
    assert result == ""


# ---------------------------------------------------------------------------
# dominant_category
# ---------------------------------------------------------------------------

def test_dominant_category_likely_constructive_wins() -> None:
    c = Counter({"likely_constructive": 3, "surrogate_or_vacuous": 5})
    # Category order places likely_constructive before surrogate_or_vacuous
    result = dominant_category(c)
    assert result == "likely_constructive"


def test_dominant_category_unknown_when_empty() -> None:
    result = dominant_category(Counter())
    assert result == "unknown"


def test_dominant_category_with_single_category() -> None:
    result = dominant_category(Counter({"neutral_definition": 2}))
    assert result == "neutral_definition"


def test_dominant_category_zero_counts_not_selected() -> None:
    c = Counter({"likely_constructive": 0, "neutral_definition": 3})
    result = dominant_category(c)
    assert result == "neutral_definition"


# ---------------------------------------------------------------------------
# replaceable_surface_mass
# ---------------------------------------------------------------------------

def test_replaceable_surface_mass_zero_when_empty() -> None:
    assert replaceable_surface_mass({}) == 0.0


def test_replaceable_surface_mass_positive_with_surrogates() -> None:
    row = {"surrogate_or_vacuous": 5, "package_reprojection": 0, "hypothesis_bridge": 0}
    result = replaceable_surface_mass(row)
    assert result > 0.0


def test_replaceable_surface_mass_additive() -> None:
    row_full = {"surrogate_or_vacuous": 2, "package_reprojection": 2, "hypothesis_bridge": 2}
    row_partial = {"surrogate_or_vacuous": 2}
    assert replaceable_surface_mass(row_full) > replaceable_surface_mass(row_partial)


# ---------------------------------------------------------------------------
# support_pressure
# ---------------------------------------------------------------------------

def test_support_pressure_zero_when_no_edges() -> None:
    assert support_pressure({}) == 0.0


def test_support_pressure_in_weighted_double() -> None:
    row = {"in_weight": 3, "out_weight": 1}
    result = support_pressure(row)
    assert result == pytest.approx(7.0)  # 2*3 + 1 = 7


def test_support_pressure_out_only() -> None:
    row = {"in_weight": 0, "out_weight": 5}
    result = support_pressure(row)
    assert result == pytest.approx(5.0)


# ---------------------------------------------------------------------------
# dominant_pressure
# ---------------------------------------------------------------------------

def test_dominant_pressure_returns_unknown_when_empty() -> None:
    assert dominant_pressure({}) == "unknown"


def test_dominant_pressure_surrogate_wins() -> None:
    row = {"surrogate_or_vacuous": 10, "package_reprojection": 0, "hypothesis_bridge": 0}
    result = dominant_pressure(row)
    assert result == "surrogate_or_vacuous"


def test_dominant_pressure_returns_non_empty_string() -> None:
    row = {"surrogate_or_vacuous": 1, "package_reprojection": 5, "hypothesis_bridge": 2}
    result = dominant_pressure(row)
    assert isinstance(result, str)
    assert len(result) > 0


# ---------------------------------------------------------------------------
# primary_action
# ---------------------------------------------------------------------------

def test_primary_action_inspect_manually_when_all_zero() -> None:
    assert primary_action({}) == "inspect manually"


def test_primary_action_surrogates_only() -> None:
    row = {"surrogate_or_vacuous": 3, "package_reprojection": 0, "hypothesis_bridge": 0}
    assert primary_action(row) == "direct constructive replacement"


def test_primary_action_surrogates_and_package() -> None:
    row = {"surrogate_or_vacuous": 2, "package_reprojection": 2, "hypothesis_bridge": 0}
    assert primary_action(row) == "replace surrogates, then collapse package layer"


def test_primary_action_hypothesis_only() -> None:
    row = {"surrogate_or_vacuous": 0, "package_reprojection": 0, "hypothesis_bridge": 5}
    assert primary_action(row) == "discharge hypothesis bridges"


def test_primary_action_package_only() -> None:
    row = {"surrogate_or_vacuous": 0, "package_reprojection": 3, "hypothesis_bridge": 0}
    assert primary_action(row) == "collapse package layer"


def test_primary_action_package_and_hypothesis() -> None:
    row = {"surrogate_or_vacuous": 0, "package_reprojection": 2, "hypothesis_bridge": 1}
    assert primary_action(row) == "construct witnesses behind packaged hypotheses"

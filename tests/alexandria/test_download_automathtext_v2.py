from __future__ import annotations

import argparse

import pytest

from tools.alexandria.download_automathtext_v2 import build_allow_patterns, make_plan, pattern_for_config


def test_pattern_for_config_supports_quality_buckets() -> None:
    assert pattern_for_config("math_web", ["90-100"]) == ["math_web/90-100/*.parquet"]


def test_full_mode_requires_explicit_allow_full() -> None:
    with pytest.raises(SystemExit):
        build_allow_patterns(
            mode="full",
            configs=[],
            quality_buckets=[],
            extra_allow=[],
            allow_full=False,
        )


def test_make_plan_default_operator_configs() -> None:
    args = argparse.Namespace(
        dataset="OpenSQZ/AutoMathText-V2",
        local_dir="external/automathtext-v2",
        revision="main",
        mode="domain",
        config=[],
        default_operator_configs=True,
        quality_bucket=["90-100"],
        allow_pattern=[],
        ignore_pattern=[],
        allow_full=False,
        token_file=None,
    )
    plan = make_plan(args)
    assert plan.configs == ["math_web", "megamath", "reasoning_qa"]
    assert "math_web/90-100/*.parquet" in plan.allow_patterns

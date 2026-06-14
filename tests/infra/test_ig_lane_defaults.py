from pathlib import Path

import sys

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str((REPO / "src").resolve()))

from igf.pipeline import build


def test_ig_pipeline_defaults_use_managed_dag_lane() -> None:
    assert build.DOCUMENTED_NODES == Path("artifacts/dag/index/decls.jsonl")
    assert build.DOCUMENTED_EDGES == Path("artifacts/dag/index/edges.jsonl")


def test_ig_pipeline_legacy_fallback_is_leantrail_projection() -> None:
    assert build.LEGACY_NODES == Path("artifacts/leantrail/arango/ig_nodes.jsonl")
    assert build.LEGACY_EDGES == Path("artifacts/leantrail/arango/ig_edges.jsonl")

import json
import subprocess
import sys
from pathlib import Path

from tools.infra.aria_concept_graph import build_concept_graph, extract_concepts


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "aria_concept_graph.py"


def _write_records(path: Path) -> None:
    rows = [
        {
            "schema": "info_geometry.leansearch_local.record.v1",
            "name": "InfoGeometry.Canonical.PositiveRay",
            "kind": "structure",
            "module": "InfoGeometry.Canonical",
            "file": "lean/InfoGeometry/Canonical/PositiveRay.lean",
            "line": 10,
            "doc": "Positive projective ray for scale-invariant geometry.",
            "type": "Type",
            "snippet": "structure PositiveRay where",
            "nameTokens": ["positive", "ray"],
            "searchTokens": ["positive", "projective", "ray", "scale", "invariant", "geometry"],
        },
        {
            "schema": "info_geometry.leansearch_local.record.v1",
            "name": "InfoGeometry.Canonical.gaugeSectionFinProb",
            "kind": "def",
            "module": "InfoGeometry.Canonical",
            "file": "lean/InfoGeometry/Canonical/IBProjective.lean",
            "line": 42,
            "doc": "Canonical probability gauge section of a projective score ray.",
            "type": "ScoreRay -> FinProb",
            "snippet": "def gaugeSectionFinProb ...",
            "nameTokens": ["gauge", "section", "fin", "prob"],
            "searchTokens": ["canonical", "probability", "gauge", "section", "projective", "score", "ray", "finprob"],
        },
    ]
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def test_extract_concepts_is_deterministic_and_bounded() -> None:
    claim = "Probability is the canonical gauge section of a positive projective ray."
    concepts = extract_concepts(claim, max_concepts=4)

    assert len(concepts) == 4
    assert concepts[0] == "probability"
    assert "canonical gauge section" in concepts
    assert len(set(concepts)) == len(concepts)


def test_build_concept_graph_grounds_with_leansearch_records(tmp_path: Path) -> None:
    records = tmp_path / "records.jsonl"
    _write_records(records)

    graph = build_concept_graph(
        claim="Probability is the canonical gauge section of a positive projective ray.",
        records=records,
        top_k=2,
        max_concepts=5,
        min_grounding_score=1.0,
    )

    assert graph["schema"] == "info_geometry.aria_concept_graph.v1"
    assert graph["authority"]["graph_is_planning_prior"] is True
    assert graph["authority"]["lean_remains_proof_authority"] is True
    assert graph["aria_model"]["top_down_grounding"] is True
    assert graph["aria_model"]["bottom_up_synthesis_readiness"] is True
    assert graph["node_count"] == 5
    assert graph["edge_count"] == 4
    assert all("dependencies" in node for node in graph["nodes"])
    assert any(node["status"] == "grounded" for node in graph["nodes"])
    assert any(node["formal_code"] for node in graph["nodes"] if node["status"] == "grounded")
    grounded_names = [
        hit["name"]
        for node in graph["nodes"]
        for hit in node["retrieval"]
    ]
    assert "InfoGeometry.Canonical.gaugeSectionFinProb" in grounded_names


def test_aria_concept_graph_cli_writes_packet(tmp_path: Path) -> None:
    records = tmp_path / "records.jsonl"
    out = tmp_path / "concept-graph.json"
    _write_records(records)

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--claim",
            "A positive projective ray admits a canonical probability gauge.",
            "--records",
            str(records),
            "--top-k",
            "2",
            "--max-concepts",
            "4",
            "--out",
            str(out),
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["claim"] == "A positive projective ray admits a canonical probability gauge."
    assert payload["node_count"] == 4
    assert payload["edges"][0]["role"] == "aria_dependency"
    assert payload["aria_model"]["graph_shape_source"].startswith("frenzymath/Aria-autoformalizer")

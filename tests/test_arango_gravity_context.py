import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TOOL = REPO / "tools" / "infra" / "arango_gravity_context.py"


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(record) + "\n" for record in records),
        encoding="utf-8",
    )


def test_gravity_context_ranks_proven_neighbor_and_excerpt(tmp_path: Path) -> None:
    lean_file = tmp_path / "lean" / "InfoGeometry" / "Analytic" / "Softmax.lean"
    lean_file.parent.mkdir(parents=True)
    lean_file.write_text(
        "\n".join(
            [
                "import Mathlib",
                "",
                "namespace InfoGeometry.Analytic",
                "",
                "/-- Proven variance identity. -/",
                "theorem deriv2_logSumExp_eq_softmaxVariance : 1 = 1 := by",
                "  rfl",
                "",
                "end InfoGeometry.Analytic",
            ]
        ),
        encoding="utf-8",
    )
    nodes = tmp_path / "nodes.jsonl"
    edges = tmp_path / "edges.jsonl"
    write_jsonl(
        nodes,
        [
            {
                "_key": "m",
                "id": "module:InfoGeometry.Analytic.Softmax",
                "name": "InfoGeometry.Analytic.Softmax",
                "kind": "Module",
                "module": "InfoGeometry.Analytic.Softmax",
                "attrs": {},
            },
            {
                "_key": "d",
                "id": "InfoGeometry.Analytic.deriv2_logSumExp_eq_softmaxVariance",
                "name": "InfoGeometry.Analytic.deriv2_logSumExp_eq_softmaxVariance",
                "kind": "Declaration",
                "module": "InfoGeometry.Analytic.Softmax",
                "module_family": "InfoGeometry.Analytic",
                "file": str(lean_file),
                "line": 6,
                "attrs": {
                    "decl_kind": "theorem",
                    "doc": "Main second-derivative identity: deriv^2(logSumExp) = variance.",
                },
            },
        ],
    )
    write_jsonl(
        edges,
        [
            {
                "src": "module:InfoGeometry.Analytic.Softmax",
                "dst": "InfoGeometry.Analytic.deriv2_logSumExp_eq_softmaxVariance",
                "kind": "contains",
                "weight": 1.0,
            }
        ],
    )

    result = subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--source",
            "jsonl",
            "--nodes",
            str(nodes),
            "--edges",
            str(edges),
            "--repo-root",
            str(tmp_path),
            "--query",
            "softmax variance logSumExp derivative",
            "--top-k",
            "1",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    packet = json.loads(result.stdout)

    assert packet["schema"] == "info_geometry.gravity_context.v1"
    assert packet["graph_source"] == "jsonl"
    assert packet["items"][0]["id"] == "InfoGeometry.Analytic.deriv2_logSumExp_eq_softmaxVariance"
    assert packet["items"][0]["decl_kind"] == "theorem"
    excerpt = packet["items"][0]["source_excerpt"]
    assert any("theorem deriv2_logSumExp_eq_softmaxVariance" in row["text"] for row in excerpt["lines"])
    assert packet["prompt_policy"]["promotion_allowed"] is False


def test_gravity_context_uses_equivalence_dictionary_to_expand_query(tmp_path: Path) -> None:
    lean_file = tmp_path / "lean" / "InfoGeometry" / "Canonical" / "Modular.lean"
    lean_file.parent.mkdir(parents=True)
    lean_file.write_text(
        "\n".join(
            [
                "import Mathlib",
                "",
                "namespace InfoGeometry.Canonical",
                "",
                "/-- Modular Hamiltonian control theorem. -/",
                "theorem modularHamiltonian_controls_flow : 1 = 1 := by",
                "  rfl",
                "",
                "end InfoGeometry.Canonical",
            ]
        ),
        encoding="utf-8",
    )
    nodes = tmp_path / "nodes.jsonl"
    edges = tmp_path / "edges.jsonl"
    equiv = tmp_path / "equivalence.json"
    write_jsonl(
        nodes,
        [
            {
                "id": "InfoGeometry.Canonical.modularHamiltonian_controls_flow",
                "name": "InfoGeometry.Canonical.modularHamiltonian_controls_flow",
                "kind": "Declaration",
                "module": "InfoGeometry.Canonical.Modular",
                "module_family": "InfoGeometry.Canonical",
                "file": str(lean_file),
                "line": 6,
                "attrs": {
                    "decl_kind": "theorem",
                    "doc": "Modular Hamiltonian controls the flow.",
                },
            },
        ],
    )
    write_jsonl(edges, [])
    equiv.write_text(
        json.dumps(
            {
                "components": [
                    {
                        "id": "EQ-test",
                        "members": [
                            "BoltzmannEntropyGenerator",
                            "InfoGeometry.Canonical.modularHamiltonian",
                        ],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--source",
            "jsonl",
            "--nodes",
            str(nodes),
            "--edges",
            str(edges),
            "--repo-root",
            str(tmp_path),
            "--equivalence-dictionary",
            str(equiv),
            "--query",
            "Boltzmann entropy generator",
            "--top-k",
            "1",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    packet = json.loads(result.stdout)

    assert packet["items"][0]["id"] == "InfoGeometry.Canonical.modularHamiltonian_controls_flow"
    assert packet["synonym_expansion"]["matched_group_count"] == 1
    assert "synonym_component" in packet["synonym_expansion"]["matched_groups"][0]["labels"]
    assert "modular" in packet["expanded_query_tokens"]
    assert "hamiltonian" in packet["expanded_query_tokens"]

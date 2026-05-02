import json
import importlib.util
import os
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TOOL = REPO / "tools" / "infra" / "arango_gravity_context.py"


def load_tool_module():
    spec = importlib.util.spec_from_file_location("arango_gravity_context_for_test", TOOL)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(record) + "\n" for record in records),
        encoding="utf-8",
    )


def test_gravity_context_loads_repo_arango_env_aliases(tmp_path: Path, monkeypatch) -> None:
    env_file = tmp_path / "configs" / "local" / "hive_arango.env"
    env_file.parent.mkdir(parents=True)
    env_file.write_text(
        "\n".join(
            [
                "ARANGO_ENDPOINT=http://127.0.0.1:9999",
                "ARANGO_DATABASE=test_geometry",
                "ARANGO_USER=test_user",
                "ARANGO_PASS='test pass'",
            ]
        ),
        encoding="utf-8",
    )

    for key in [
        "HIVE_ARANGO_ENV_FILE",
        "ARANGO_ENDPOINT",
        "ARANGO_DATABASE",
        "ARANGO_USER",
        "ARANGO_USERNAME",
        "ARANGO_PASS",
        "ARANGO_PASSWORD",
    ]:
        monkeypatch.delenv(key, raising=False)

    module = load_tool_module()
    loaded = module.load_repo_arango_env(tmp_path)

    assert loaded == env_file
    assert os.environ["ARANGO_ENDPOINT"] == "http://127.0.0.1:9999"
    assert os.environ["ARANGO_DATABASE"] == "test_geometry"
    assert os.environ["ARANGO_USER"] == "test_user"
    assert os.environ["ARANGO_USERNAME"] == "test_user"
    assert os.environ["ARANGO_PASS"] == "test pass"
    assert os.environ["ARANGO_PASSWORD"] == "test pass"


def test_igf_config_and_legacy_arango_env_resolve_same_config(
    tmp_path: Path, monkeypatch
) -> None:
    env_file = tmp_path / "hive_arango.env"
    env_file.write_text(
        "\n".join(
            [
                "ARANGO_ENDPOINT=http://127.0.0.1:7777",
                "ARANGO_DATABASE=igf_config_test",
                "ARANGO_USERNAME=legacy_user",
                "ARANGO_PASSWORD='legacy pass'",
            ]
        ),
        encoding="utf-8",
    )
    for key in [
        "HIVE_ARANGO_ENV_FILE",
        "ARANGO_ENDPOINT",
        "ARANGO_DATABASE",
        "ARANGO_USER",
        "ARANGO_USERNAME",
        "ARANGO_PASS",
        "ARANGO_PASSWORD",
    ]:
        monkeypatch.delenv(key, raising=False)
    monkeypatch.setenv("HIVE_ARANGO_ENV_FILE", str(env_file))

    sys.path.insert(0, str((REPO / "src").resolve()))
    from igf.config import load_arango_config
    from tools.infra import arango_env

    package_cfg = load_arango_config(tmp_path)

    assert arango_env.load_repo_arango_env(tmp_path) == env_file
    assert package_cfg.endpoint == arango_env.arango_endpoint()
    assert package_cfg.database == arango_env.arango_database()
    assert package_cfg.user == arango_env.arango_username()
    assert package_cfg.password == arango_env.arango_password()


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
                    "rep_depth_nat": 4,
                    "rep_depth_slug": "transport",
                    "rep_layer": "L4_ModularTransport",
                    "rep_layer_description": "modular/transport/flow substrate",
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
    assert packet["items"][0]["rep_layer"] == "L4_ModularTransport"
    assert packet["items"][0]["rep_depth"] == 4
    assert packet["items"][0]["rep_depth_slug"] == "transport"
    assert packet["graph_rep_layer_counts"] == [
        {"rep_layer": None, "count": 1, "rep_depths": [], "rep_depth_slugs": []},
        {
            "rep_layer": "L4_ModularTransport",
            "count": 1,
            "rep_depths": [4],
            "rep_depth_slugs": ["transport"],
        },
    ]
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


def test_gravity_context_can_filter_by_rep_layer(tmp_path: Path) -> None:
    lean_file = tmp_path / "lean" / "InfoGeometry" / "Canonical" / "Layered.lean"
    lean_file.parent.mkdir(parents=True)
    lean_file.write_text(
        "\n".join(
            [
                "import Mathlib",
                "",
                "namespace InfoGeometry.Canonical",
                "",
                "theorem modular_transport_surface : 1 = 1 := by",
                "  rfl",
                "",
                "theorem operator_surface : 1 = 1 := by",
                "  rfl",
                "",
                "end InfoGeometry.Canonical",
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
                "id": "InfoGeometry.Canonical.modular_transport_surface",
                "name": "InfoGeometry.Canonical.modular_transport_surface",
                "kind": "Declaration",
                "module": "InfoGeometry.Canonical.Layered",
                "file": str(lean_file),
                "line": 5,
                "attrs": {
                    "decl_kind": "theorem",
                    "doc": "modular transport surface",
                    "rep_depth_nat": 4,
                    "rep_depth_slug": "transport",
                    "rep_layer": "L4_ModularTransport",
                },
            },
            {
                "id": "InfoGeometry.Canonical.operator_surface",
                "name": "InfoGeometry.Canonical.operator_surface",
                "kind": "Declaration",
                "module": "InfoGeometry.Canonical.Layered",
                "file": str(lean_file),
                "line": 8,
                "attrs": {
                    "decl_kind": "theorem",
                    "doc": "operator surface",
                    "rep_depth_nat": 2,
                    "rep_depth_slug": "operator",
                    "rep_layer": "L2_Operator",
                },
            },
        ],
    )
    write_jsonl(edges, [])

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
            "surface",
            "--min-seed-score",
            "0.1",
            "--rep-layer",
            "L2_Operator",
            "--top-k",
            "4",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    packet = json.loads(result.stdout)

    assert packet["requested_rep_layers"] == ["L2_Operator"]
    assert [item["id"] for item in packet["items"]] == ["InfoGeometry.Canonical.operator_surface"]
    assert packet["result_rep_layer_counts"] == [
        {
            "rep_layer": "L2_Operator",
            "count": 1,
            "rep_depths": [2],
            "rep_depth_slugs": ["operator"],
        }
    ]


def test_gravity_context_uses_spectral_edge_priors_without_promotion(tmp_path: Path) -> None:
    lean_file = tmp_path / "lean" / "InfoGeometry" / "OperatorAlgebra" / "Closure.lean"
    lean_file.parent.mkdir(parents=True)
    lean_file.write_text(
        "\n".join(
            [
                "import Mathlib",
                "",
                "namespace InfoGeometry.OperatorAlgebra",
                "",
                "theorem closure_seed : 1 = 1 := by",
                "  rfl",
                "",
                "theorem closure_good_neighbor : 1 = 1 := by",
                "  rfl",
                "",
                "theorem closure_unsafe_neighbor : 1 = 1 := by",
                "  rfl",
                "",
                "end InfoGeometry.OperatorAlgebra",
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
                "id": "InfoGeometry.OperatorAlgebra.closure_seed",
                "name": "InfoGeometry.OperatorAlgebra.closure_seed",
                "kind": "Declaration",
                "module": "InfoGeometry.OperatorAlgebra.Closure",
                "file": str(lean_file),
                "line": 5,
                "attrs": {"decl_kind": "theorem", "doc": "closure seed"},
            },
            {
                "id": "InfoGeometry.OperatorAlgebra.closure_good_neighbor",
                "name": "InfoGeometry.OperatorAlgebra.closure_good_neighbor",
                "kind": "Declaration",
                "module": "InfoGeometry.OperatorAlgebra.Closure",
                "file": str(lean_file),
                "line": 8,
                "attrs": {"decl_kind": "theorem", "doc": "neighbor"},
                "energy": {"term_size": 9, "redex_count": 1},
            },
            {
                "id": "InfoGeometry.OperatorAlgebra.closure_unsafe_neighbor",
                "name": "InfoGeometry.OperatorAlgebra.closure_unsafe_neighbor",
                "kind": "Declaration",
                "module": "InfoGeometry.OperatorAlgebra.Closure",
                "file": str(lean_file),
                "line": 11,
                "attrs": {"decl_kind": "theorem", "doc": "neighbor"},
                "energy": {"term_size": 9, "redex_count": 1, "unsafe_penalty": 4},
            },
        ],
    )
    write_jsonl(
        edges,
        [
            {
                "src": "InfoGeometry.OperatorAlgebra.closure_seed",
                "dst": "InfoGeometry.OperatorAlgebra.closure_good_neighbor",
                "kind": "depends_on",
                "weight": 1.0,
                "action_weight": 0.1,
                "proof_weight": 1.0,
            },
            {
                "src": "InfoGeometry.OperatorAlgebra.closure_seed",
                "dst": "InfoGeometry.OperatorAlgebra.closure_unsafe_neighbor",
                "kind": "analogy_to",
                "weight": 1.0,
                "action_weight": 0.1,
                "unsafe_penalty": 8.0,
            },
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
            "closure seed",
            "--top-k",
            "3",
            "--max-hops",
            "1",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    packet = json.loads(result.stdout)
    ids = [item["id"] for item in packet["items"]]

    assert ids.index("InfoGeometry.OperatorAlgebra.closure_good_neighbor") < ids.index(
        "InfoGeometry.OperatorAlgebra.closure_unsafe_neighbor"
    )
    assert packet["prompt_policy"]["promotion_allowed"] is False
    assert packet["prompt_policy"]["spectral_weights"]["enabled"] is True
    unsafe = next(item for item in packet["items"] if item["id"].endswith("closure_unsafe_neighbor"))
    assert unsafe["energy"]["unsafe_penalty"] == 4.0

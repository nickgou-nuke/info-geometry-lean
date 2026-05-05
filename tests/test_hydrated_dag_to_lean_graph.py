import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "hydrated_dag_to_lean_graph.py"


def _write_fixture(path: Path) -> None:
    payload = {
        "components": [
            {
                "componentId": "C0",
                "componentIndex": 0,
                "representative": "Fixture.Root",
                "members": ["Fixture.Root"],
                "dependencyComponentIds": [],
                "reverseDependentComponentIds": ["C1"],
                "isRoot": True,
                "isCapstone": False,
                "size": 1,
                "depthMin": 0,
                "depthMax": 0,
                "strictDominatorCount": 0,
            },
            {
                "componentId": "C1",
                "componentIndex": 1,
                "representative": "Fixture.Middle",
                "members": ["Fixture.Middle"],
                "dependencyComponentIds": ["C0"],
                "reverseDependentComponentIds": ["C2"],
                "isRoot": False,
                "isCapstone": False,
                "size": 1,
                "depthMin": 1,
                "depthMax": 1,
                "strictDominatorCount": 1,
            },
            {
                "componentId": "C2",
                "componentIndex": 2,
                "representative": "Fixture.Capstone",
                "members": ["Fixture.Capstone"],
                "dependencyComponentIds": ["C1"],
                "reverseDependentComponentIds": [],
                "isRoot": False,
                "isCapstone": True,
                "size": 1,
                "depthMin": 2,
                "depthMax": 2,
                "strictDominatorCount": 0,
            },
        ]
    }
    path.write_text(json.dumps(payload), encoding="utf-8")


def _component(
    cid: str,
    index: int,
    representative: str,
    *,
    deps: list[str] | None = None,
    users: list[str] | None = None,
) -> dict:
    return {
        "componentId": cid,
        "componentIndex": index,
        "representative": representative,
        "members": [representative],
        "dependencyComponentIds": deps or [],
        "reverseDependentComponentIds": users or [],
        "isRoot": not deps,
        "isCapstone": not users,
        "size": 1,
        "depthMin": index,
        "depthMax": index,
        "strictDominatorCount": 0,
    }


def _run_adapter(structure: Path, out: Path, *extra: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--structure",
            str(structure),
            "--out",
            str(out),
            *extra,
        ],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
    )


def test_hydrated_dag_to_lean_graph_apex_slice_has_closed_references_and_meta(tmp_path: Path) -> None:
    structure = tmp_path / "structural-topology.json"
    out = tmp_path / "fixture-cone.json"
    _write_fixture(structure)

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--structure",
            str(structure),
            "--apex",
            "Fixture.Middle",
            "--backward-depth",
            "1",
            "--forward-depth",
            "1",
            "--max-nodes",
            "10",
            "--out",
            str(out),
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    rows = json.loads(out.read_text(encoding="utf-8"))
    meta = json.loads(out.with_suffix(".meta.json").read_text(encoding="utf-8"))

    names = {row["name"] for row in rows}
    assert names == {"Fixture.Root", "Fixture.Middle", "Fixture.Capstone"}

    refs_by_name = {row["name"]: row["references"] for row in rows}
    assert refs_by_name["Fixture.Root"] == []
    assert refs_by_name["Fixture.Middle"] == ["Fixture.Root"]
    assert refs_by_name["Fixture.Capstone"] == ["Fixture.Middle"]

    for row in rows:
        for ref in row["references"]:
            assert ref in names
            assert ref != row["name"]

    assert meta["orientation"] == "lean-graph references = dependencies"
    assert meta["source_orientation"] == "structural-topology component -> dependencyComponentIds"
    assert meta["node_semantics"] == "SCC representative, not raw declaration"
    assert meta["slice_mode"] == "apex_cone"
    assert meta["apex"] == "Fixture.Middle"
    assert meta["node_count"] == 3
    assert meta["validation"]["valid_for_lean_graph"] is True
    assert meta["validation"]["missing_reference_count"] == 0
    assert meta["validation"]["self_reference_count"] == 0
    assert meta["validation"]["duplicate_name_count"] == 0


def test_hydrated_dag_to_lean_graph_fails_fast_on_duplicate_representatives(tmp_path: Path) -> None:
    structure = tmp_path / "duplicate-structural-topology.json"
    out = tmp_path / "duplicate.json"
    structure.write_text(
        json.dumps(
            {
                "components": [
                    _component("C0", 0, "Fixture.Duplicate"),
                    _component("C1", 1, "Fixture.Duplicate", deps=["C0"]),
                ]
            }
        ),
        encoding="utf-8",
    )

    result = _run_adapter(structure, out, "--max-nodes", "10")

    assert result.returncode != 0
    assert "duplicate_names=1" in result.stderr
    assert not out.exists()


def test_hydrated_dag_to_lean_graph_fails_fast_on_self_dependency(tmp_path: Path) -> None:
    structure = tmp_path / "self-structural-topology.json"
    out = tmp_path / "self.json"
    structure.write_text(
        json.dumps(
            {
                "components": [
                    _component("C0", 0, "Fixture.Self", deps=["C0"], users=["C0"]),
                ]
            }
        ),
        encoding="utf-8",
    )

    result = _run_adapter(structure, out, "--max-nodes", "10")

    assert result.returncode != 0
    assert "self_refs=1" in result.stderr
    assert not out.exists()

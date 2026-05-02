import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest


REPO = Path(__file__).resolve().parents[2]
CLI = REPO / "cli" / "igf.py"
PYTHON = shutil.which("python3") or sys.executable


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(r) + "\n" for r in rows), encoding="utf-8")


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def make_minimal_artifacts(base: Path) -> Path:
    d = base / "artifacts"
    write_jsonl(
        d / "ig_patch_runs.jsonl",
        [{"_key": "run_1", "run_id": "run_1", "schema_version": "ig.patch_run.v1", "created_at": "2026-01-01T00:00:00Z", "source_graph_hash": "h", "algorithm_version": "chiral_patch_hashes.v1.2", "authority_level": "derived", "claim_scope": "derived_spectral_neighborhood_sidecar", "non_overclaim": True}],
    )
    write_jsonl(
        d / "ig_chiral_patches.jsonl",
        [{"_key": "patch_1", "patch_id": "patch_1", "run_id": "run_1", "schema_version": "ig.chiral_patch.v1.2", "patch_type": "ego_patch", "node_count": 2, "edge_count": 1, "coarse_hash": "sha256:test", "chiral_entropy": 0.0, "chiral_bias": 0.0, "authority_level": "derived", "claim_scope": "derived_spectral_neighborhood_sidecar", "non_overclaim": True}],
    )
    write_jsonl(
        d / "ig_patch_spectral_signatures.jsonl",
        [{"_key": "patch_1", "patch_id": "patch_1", "run_id": "run_1", "schema_version": "ig.patch_spectral_signature.v1.2", "eigenvalues": [1.0], "nullity": 0, "pseudo_logdet": 0.0, "spectral_status": "exact", "authority_level": "derived", "claim_scope": "derived_spectral_neighborhood_sidecar", "non_overclaim": True}],
    )
    write_jsonl(
        d / "ig_patch_members.jsonl",
        [{"_from": "ig_chiral_patches/patch_1", "_to": "ig_nodes/A", "patch_id": "patch_1", "run_id": "run_1", "schema_version": "ig.patch_member.v1", "membership_type": "ego"}],
    )
    write_jsonl(
        d / "ig_patch_edges.jsonl",
        [{"_from": "ig_chiral_patches/patch_1", "_to": "ig_chiral_patches/patch_1", "from_patch_id": "patch_1", "to_patch_id": "patch_1", "run_id": "run_1", "schema_version": "ig.patch_edge.v1", "edge_type": "PATCH_DEPENDS_ON"}],
    )
    return d


def test_validate_strict_passes_on_minimal_greenfield_fixture(tmp_path: Path) -> None:
    artifacts = make_minimal_artifacts(tmp_path)
    result = subprocess.run(
        [
            PYTHON,
            str(CLI),
            "validate",
            "--dir",
            str(artifacts),
            "--schemas-dir",
            str(REPO / "schemas"),
            "--strict",
            "--print-json",
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0
    payload = json.loads(result.stdout)
    assert payload["ok"] is True
    assert payload["error_count"] == 0


def test_validate_strict_fails_when_member_run_id_missing(tmp_path: Path) -> None:
    artifacts = make_minimal_artifacts(tmp_path)
    rows = read_jsonl(artifacts / "ig_patch_members.jsonl")
    rows[0].pop("run_id")
    write_jsonl(artifacts / "ig_patch_members.jsonl", rows)

    result = subprocess.run(
        [
            PYTHON,
            str(CLI),
            "validate",
            "--dir",
            str(artifacts),
            "--schemas-dir",
            str(REPO / "schemas"),
            "--strict",
            "--max-errors",
            "5",
            "--print-json",
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 1
    payload = json.loads(result.stdout)
    assert payload["ok"] is False
    assert any("valid under any" in e["error"] for e in payload["errors"])


def test_validate_strict_accepts_patch_run_id_legacy_alias(tmp_path: Path) -> None:
    artifacts = make_minimal_artifacts(tmp_path)
    for name in [
        "ig_patch_runs.jsonl",
        "ig_chiral_patches.jsonl",
        "ig_patch_spectral_signatures.jsonl",
        "ig_patch_members.jsonl",
        "ig_patch_edges.jsonl",
    ]:
        rows = read_jsonl(artifacts / name)
        for row in rows:
            row["patch_run_id"] = row.pop("run_id")
        write_jsonl(artifacts / name, rows)

    result = subprocess.run(
        [
            PYTHON,
            str(CLI),
            "validate",
            "--dir",
            str(artifacts),
            "--schemas-dir",
            str(REPO / "schemas"),
            "--strict",
            "--print-json",
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0
    payload = json.loads(result.stdout)
    assert payload["ok"] is True


def test_validate_strict_rejects_formal_authority_without_proof_link(tmp_path: Path) -> None:
    artifacts = make_minimal_artifacts(tmp_path)
    rows = read_jsonl(artifacts / "ig_chiral_patches.jsonl")
    rows[0]["authority_level"] = "formal"
    write_jsonl(artifacts / "ig_chiral_patches.jsonl", rows)

    result = subprocess.run(
        [
            PYTHON,
            str(CLI),
            "validate",
            "--dir",
            str(artifacts),
            "--schemas-dir",
            str(REPO / "schemas"),
            "--strict",
            "--max-errors",
            "10",
            "--print-json",
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 1
    payload = json.loads(result.stdout)
    assert payload["ok"] is False
    assert any("proof_link" in e["error"] for e in payload["errors"])


def test_normalize_backfills_member_and_edge_fields(tmp_path: Path) -> None:
    inp = tmp_path / "in"
    out = tmp_path / "out"

    write_jsonl(
        inp / "ig_patch_runs.jsonl",
        [{"_key": "run_999", "schema_version": "ig.patch_run.v1", "created_at": "2026-01-01", "source_graph_hash": "h", "algorithm_version": "a"}],
    )
    write_jsonl(
        inp / "ig_chiral_patches.jsonl",
        [{"_key": "patch_ego_run_999_decl", "patch_id": "patch_ego_run_999_decl", "run_id": "run_999", "schema_version": "ig.chiral_patch.v1.2", "patch_type": "ego_patch", "node_count": 2, "edge_count": 1, "coarse_hash": "sha256:test", "chiral_entropy": 0.0, "chiral_bias": 0.0, "claim_scope": "derived_spectral_neighborhood_sidecar", "non_overclaim": True}],
    )
    write_jsonl(inp / "ig_patch_spectral_signatures.jsonl", [{"_key": "patch_ego_run_999_decl", "patch_id": "patch_ego_run_999_decl", "eigenvalues": [1.0], "nullity": 0, "pseudo_logdet": 0.0}])
    write_jsonl(inp / "ig_patch_members.jsonl", [{"_from": "ig_chiral_patches/patch_ego_run_999_decl", "_to": "ig_nodes/X", "membership_type": "ego"}])
    write_jsonl(inp / "ig_patch_edges.jsonl", [{"_from": "ig_chiral_patches/patch_ego_run_999_decl", "_to": "ig_chiral_patches/patch_ego_run_999_decl", "edge_type": "PATCH_DEPENDS_ON"}])

    result = subprocess.run(
        [
            PYTHON,
            str(CLI),
            "normalize",
            "--input-dir",
            str(inp),
            "--output-dir",
            str(out),
            "--print-json",
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0

    m = read_jsonl(out / "ig_patch_members.jsonl")[0]
    e = read_jsonl(out / "ig_patch_edges.jsonl")[0]
    s = read_jsonl(out / "ig_patch_spectral_signatures.jsonl")[0]
    r = read_jsonl(out / "ig_patch_runs.jsonl")[0]
    p = read_jsonl(out / "ig_chiral_patches.jsonl")[0]

    assert m["run_id"] == "run_999"
    assert m["patch_id"] == "patch_ego_run_999_decl"
    assert e["run_id"] == "run_999"
    assert e["from_patch_id"] == "patch_ego_run_999_decl"
    assert e["to_patch_id"] == "patch_ego_run_999_decl"
    assert s["run_id"] == "run_999"
    assert r["authority_level"] == "derived"
    assert p["authority_level"] == "derived"
    assert s["authority_level"] == "derived"
    assert s["non_overclaim"] is True
    assert m["_key"]
    assert e["_key"]


def test_run_id_normalization_and_stable_keys_are_deterministic() -> None:
    sys.path.insert(0, str((REPO / "src").resolve()))
    from igf.artifacts.compatibility_adapters import normalize_run_id, stable_key

    row = normalize_run_id({"patch_run_id": "patch_run_1", "patch_id": "p"})
    assert row["run_id"] == "patch_run_1"

    fields = ["run_id", "patch_id", "_from", "_to", "membership_type"]
    a = {
        "run_id": "patch_run_1",
        "patch_id": "p",
        "_from": "ig_chiral_patches/p",
        "_to": "ig_nodes/A",
        "membership_type": "ego",
    }
    b = dict(reversed(list(a.items())))
    assert stable_key(a, fields) == stable_key(b, fields)


def test_query_registry_has_required_queries() -> None:
    sys.path.insert(0, str((REPO / "src").resolve()))
    from igf.graph.query_registry import QUERIES, get_query

    required = {
        "verify.run_summary",
        "verify.latest_run_id",
        "verify.orphan_spectral",
        "verify.orphan_members",
        "verify.orphan_patch_edges",
        "patch.maxent_style_candidates",
        "patch.maxent_candidate_ground_states",
    }
    assert required.issubset(set(QUERIES))
    q = get_query("verify.run_summary")
    assert "run_id" in q.aql

    maxent = get_query("patch.maxent_style_candidates")
    assert "derived_spectral_neighborhood_sidecar" in maxent.aql
    assert "non_overclaim" in maxent.aql
    assert "chiral_entropy" in maxent.aql
    assert "pseudo_logdet" in maxent.aql

    compat = get_query("patch.maxent_candidate_ground_states")
    assert compat.aql == maxent.aql


def test_maxent_candidate_pipeline_uses_safe_query(monkeypatch: pytest.MonkeyPatch) -> None:
    sys.path.insert(0, str((REPO / "src").resolve()))
    from igf.pipeline import candidates

    calls = []

    monkeypatch.setattr(candidates, "resolve_run_id", lambda db, run_id: run_id or "run_latest")

    def fake_run_query(db, query_id, **bind_vars):
        calls.append((query_id, bind_vars))
        return [{"patch_id": "p1"}]

    monkeypatch.setattr(candidates, "run_query", fake_run_query)

    result = candidates.find_maxent_style_patch_candidates(
        object(), limit=3, min_abs_chiral_bias=0.25
    )

    assert result["ok"] is True
    assert result["query_id"] == "patch.maxent_style_candidates"
    assert result["non_overclaim"] is True
    assert result["candidate_count"] == 1
    assert calls == [
        (
            "patch.maxent_style_candidates",
            {"run_id": "run_latest", "limit": 3, "min_abs_chiral_bias": 0.25},
        )
    ]


def test_preflight_reports_missing_credentials(monkeypatch: pytest.MonkeyPatch) -> None:
    sys.path.insert(0, str((REPO / "src").resolve()))
    from igf.config.preflight import run_preflight

    for key in ["ARANGO_USER", "ARANGO_USERNAME", "ARANGO_PASS", "ARANGO_PASSWORD"]:
        monkeypatch.delenv(key, raising=False)

    result = run_preflight()
    assert result["ok"] is False
    assert result["error"] == "missing_credentials"

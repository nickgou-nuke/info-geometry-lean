import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "tools" / "run_leansearch_safe.sh"


def _write_records(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "schema": "info_geometry.leansearch_local.record.v1",
                "name": "Demo.tensorFactorSeparation",
                "kind": "theorem",
                "module": "Demo",
                "file": "lean/Demo.lean",
                "line": 7,
                "doc": "Tensor factor separation owner for Cuntz and K operators.",
                "type": "(S \\otimes id) * (id \\otimes K) = (id \\otimes K) * (S \\otimes id)",
                "snippet": "theorem tensorFactorSeparation : True := by trivial",
                "nameTokens": ["demo", "tensor", "factor", "separation"],
                "searchTokens": ["demo", "tensor", "factor", "separation", "cuntz", "operator"],
            }
        )
        + "\n",
        encoding="utf-8",
    )


def _env(records: Path) -> dict[str, str]:
    env = os.environ.copy()
    env["LEANSEARCH_RECORDS"] = str(records)
    env["LEANSEARCH_PYTHON_BIN"] = sys.executable
    env["LEANSEARCH_DEFAULT_NUM"] = "3"
    return env


def test_run_leansearch_safe_search_uses_local_records(tmp_path: Path) -> None:
    records = tmp_path / "records.jsonl"
    _write_records(records)

    proc = subprocess.run(
        ["bash", str(WRAPPER), "search", "tensor factor Cuntz", "--top-k", "1"],
        cwd=ROOT,
        env=_env(records),
        check=True,
        text=True,
        capture_output=True,
    )

    payload = json.loads(proc.stdout)
    assert payload["schema"] == "info_geometry.leansearch_local.search_result.v1"
    assert payload["records"] == str(records)
    assert payload["hits"][0]["name"] == "Demo.tensorFactorSeparation"


def test_run_leansearch_safe_bare_query_defaults_to_local_search(tmp_path: Path) -> None:
    records = tmp_path / "records.jsonl"
    _write_records(records)

    proc = subprocess.run(
        ["bash", str(WRAPPER), "Cuntz operator separation"],
        cwd=ROOT,
        env=_env(records),
        check=True,
        text=True,
        capture_output=True,
    )

    payload = json.loads(proc.stdout)
    assert payload["topK"] == 3
    assert payload["hits"][0]["name"] == "Demo.tensorFactorSeparation"


def test_run_leansearch_safe_health_reports_local_inputs(tmp_path: Path) -> None:
    records = tmp_path / "records.jsonl"
    decls = tmp_path / "decls.jsonl"
    types = tmp_path / "types.jsonl"
    _write_records(records)
    decls.write_text("", encoding="utf-8")
    types.write_text("", encoding="utf-8")
    env = _env(records)
    env["LEANSEARCH_DECLS"] = str(decls)
    env["LEANSEARCH_TYPES"] = str(types)

    proc = subprocess.run(
        ["bash", str(WRAPPER), "health"],
        cwd=ROOT,
        env=env,
        check=True,
        text=True,
        capture_output=True,
    )

    assert "leansearch_safe=ok" in proc.stdout
    assert f"records={records}" in proc.stdout


def test_run_leansearch_safe_build_source_external_root(tmp_path: Path) -> None:
    source_root = tmp_path / "spin"
    dag_dir = source_root / "DAG"
    dag_dir.mkdir(parents=True)
    (dag_dir / "DiracLaplacian.lean").write_text(
        "\n".join(
            [
                "namespace DAG.DiracLaplacian",
                "theorem dirac_square_check_chain : True := by",
                "  trivial",
                "end DAG.DiracLaplacian",
            ]
        ),
        encoding="utf-8",
    )
    records = tmp_path / "source_records.jsonl"

    proc = subprocess.run(
        [
            "bash",
            str(WRAPPER),
            "build-source",
            "--source-root",
            str(source_root),
            "--out",
            str(records),
        ],
        cwd=ROOT,
        env=_env(records),
        check=True,
        text=True,
        capture_output=True,
    )

    payload = json.loads(proc.stdout)
    assert payload["schema"] == "info_geometry.leansearch_local.source_build_summary.v1"
    assert payload["records"] == 1

    proc = subprocess.run(
        ["bash", str(WRAPPER), "search", "dirac_square_check_chain", "--top-k", "1"],
        cwd=ROOT,
        env=_env(records),
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["hits"][0]["schema"] == "info_geometry.leansearch_local.source_record.v1"
    assert payload["hits"][0]["authority"] == "source-navigation-only"
    assert payload["hits"][0]["name"] == "DAG.DiracLaplacian.dirac_square_check_chain"

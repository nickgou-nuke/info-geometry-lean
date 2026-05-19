from __future__ import annotations

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tools" / "infra" / "graph_rag_query.py"


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["python3", str(SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def test_graph_rag_json_smoke() -> None:
    proc = run("Weyl character formula", "--top-k", "3", "--no-gravity", "--format", "json")
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["query"] == "Weyl character formula"
    assert isinstance(payload.get("lean"), list)
    assert isinstance(payload.get("docs"), list)
    assert isinstance(payload.get("external"), list)
    assert payload["lean"], "expected Lean hits"
    assert payload["docs"], "expected docs hits"


def test_graph_rag_cli_sections_and_gravity_toggle() -> None:
    proc = run("Weyl character formula", "--top-k", "3", "--no-gravity")
    assert proc.returncode == 0, proc.stderr
    stdout = proc.stdout.lower()
    assert "## lean declarations" in stdout
    assert "## docs / black books / handover" in stdout
    assert "## external mirrors" in stdout
    assert "## gravity context" not in stdout

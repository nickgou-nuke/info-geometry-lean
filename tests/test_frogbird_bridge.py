import json
import subprocess
import sys
from pathlib import Path

from tools.infra.frogbird_bridge import build_bridge

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "frogbird_bridge.py"


def test_build_bridge_creates_external_ref_files(tmp_path: Path) -> None:
    source = tmp_path / "theorem_index.json"
    source.write_text(
        json.dumps(
            {
                "commit": "deadbeef",
                "stats": {"files": 2, "decls": 3},
                "declarations": [
                    {"file": "src/Foo.lean", "line": 1, "decl": "foo", "stmt": "theorem foo : True := by"},
                    {"file": "src/Bar.lean", "line": 2, "decl": "bar", "stmt": "def bar : Nat := 0"},
                ],
            }
        ),
        encoding="utf-8",
    )
    out = tmp_path / "out"

    summary = build_bridge(source_path=source, output_dir=out)

    assert summary["declarations"] == 2
    assert (out / "index.json").exists()
    assert (out / "keyword_index.json").exists()
    index = json.loads((out / "index.json").read_text(encoding="utf-8"))
    assert index["declarations"][0]["retrieval_only"] is True
    assert index["declarations"][0]["context_only"] is True


def test_frogbird_bridge_cli_writes_outputs(tmp_path: Path) -> None:
    source = tmp_path / "theorem_index.json"
    source.write_text(
        json.dumps(
            {
                "commit": "deadbeef",
                "stats": {"files": 1, "decls": 1},
                "declarations": [
                    {"file": "src/Foo.lean", "line": 1, "decl": "foo", "stmt": "theorem foo : True := by"},
                ],
            }
        ),
        encoding="utf-8",
    )
    out = tmp_path / "out"

    subprocess.run(
        [sys.executable, str(SCRIPT), "--source", str(source), "--output-dir", str(out)],
        cwd=REPO_ROOT,
        check=True,
    )

    summary = json.loads((out / "bridge_summary.json").read_text(encoding="utf-8"))
    assert summary["declarations"] == 1
    assert summary["terms"] >= 1

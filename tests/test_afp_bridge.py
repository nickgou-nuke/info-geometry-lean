import json
import subprocess
import sys
from pathlib import Path

from tools.infra.afp_bridge import build_bridge

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "afp_bridge.py"


def test_build_bridge_indexes_afp_files(tmp_path: Path) -> None:
    source = tmp_path / "afp"
    thys = source / "thys" / "Toy"
    thys.mkdir(parents=True)
    (source / "etc").mkdir(parents=True)
    (source / "etc" / "version").write_text("VERSION=2025-2\n", encoding="utf-8")
    (thys / "Toy.thy").write_text(
        """
        theory Toy imports Main begin
        theorem toy_theorem: True by simp
        definition toy_def where "toy_def = True"
        end
        """,
        encoding="utf-8",
    )
    out = tmp_path / "out"

    summary = build_bridge(source_root=source, output_dir=out)

    assert summary["files"] == 1
    assert summary["declarations"] >= 2
    assert (out / "index.json").exists()
    assert (out / "keyword_index.json").exists()
    index = json.loads((out / "index.json").read_text(encoding="utf-8"))
    assert index["status"]["version"] == "2025-2"
    assert index["declarations"][0]["retrieval_only"] is True
    assert index["declarations"][0]["context_only"] is True


def test_afp_bridge_cli_writes_outputs(tmp_path: Path) -> None:
    source = tmp_path / "afp"
    thys = source / "thys" / "Toy"
    thys.mkdir(parents=True)
    (source / "etc").mkdir(parents=True)
    (source / "etc" / "version").write_text("VERSION=2025-2\n", encoding="utf-8")
    (thys / "Toy.thy").write_text(
        """
        theory Toy imports Main begin
        theorem toy_theorem: True by simp
        end
        """,
        encoding="utf-8",
    )
    out = tmp_path / "out"

    subprocess.run(
        [sys.executable, str(SCRIPT), "--source", str(source), "--output-dir", str(out)],
        cwd=REPO_ROOT,
        check=True,
    )

    summary = json.loads((out / "bridge_summary.json").read_text(encoding="utf-8"))
    assert summary["declarations"] >= 1
    assert summary["terms"] >= 1

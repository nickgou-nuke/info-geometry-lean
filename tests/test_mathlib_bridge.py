import json
import subprocess
import sys
from pathlib import Path

from tools.infra.mathlib_bridge import build_bridge

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "mathlib_bridge.py"


def test_build_bridge_indexes_mathlib_files(tmp_path: Path) -> None:
    source = tmp_path / "mathlib"
    (source / "Mathlib" / "Toy").mkdir(parents=True)
    (source / "Mathlib" / "Toy" / "Example.lean").write_text(
        """
        theorem toyTheorem : True := by
          trivial

        def toyDef : Nat := 0
        """,
        encoding="utf-8",
    )
    (source / "lean-toolchain").write_text("leanprover/lean4:v4.28.0\n", encoding="utf-8")
    (source / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
    (source / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
    out = tmp_path / "out"

    summary = build_bridge(source_root=source, output_dir=out)

    assert summary["files"] == 1
    assert summary["declarations"] >= 2
    assert (out / "index.json").exists()
    assert (out / "keyword_index.json").exists()
    index = json.loads((out / "index.json").read_text(encoding="utf-8"))
    assert index["status"]["lean_toolchain"] == "leanprover/lean4:v4.28.0"
    assert index["declarations"][0]["retrieval_only"] is True
    assert index["declarations"][0]["context_only"] is True


def test_mathlib_bridge_cli_writes_outputs(tmp_path: Path) -> None:
    source = tmp_path / "mathlib"
    (source / "Mathlib" / "Toy").mkdir(parents=True)
    (source / "Mathlib" / "Toy" / "Example.lean").write_text(
        """
        theorem toyTheorem : True := by
          trivial
        """,
        encoding="utf-8",
    )
    (source / "lean-toolchain").write_text("leanprover/lean4:v4.28.0\n", encoding="utf-8")
    (source / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
    (source / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
    out = tmp_path / "out"

    subprocess.run(
        [sys.executable, str(SCRIPT), "--source", str(source), "--output-dir", str(out)],
        cwd=REPO_ROOT,
        check=True,
    )

    summary = json.loads((out / "bridge_summary.json").read_text(encoding="utf-8"))
    assert summary["declarations"] >= 1
    assert summary["terms"] >= 1

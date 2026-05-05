import json
import subprocess
import sys
from pathlib import Path

from tools.infra.millennium_problem_bridge import build_records, extract_status_table, run_bridge


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "millennium_problem_bridge.py"


def _fixture_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "LeanMillenniumPrizeProblems"
    problem_dir = repo / "Problems" / "RiemannHypothesis"
    problem_dir.mkdir(parents=True)
    (repo / "README.md").write_text(
        """
| Problem | Main Lean statement | Location | Status | Clay fidelity |
|---|---|---|---|---|
| Riemann Hypothesis | `Millennium.RiemannHypothesis` | `Problems/RiemannHypothesis/Millennium.lean` | Statement | Direct |
""",
        encoding="utf-8",
    )
    (problem_dir / "Millennium.lean").write_text(
        """
namespace Millennium

def CriticalLine : Prop := True

theorem riemannHypothesis_iff_mathlib : True := by
  trivial

def RiemannHypothesis : Prop := True

end Millennium
""",
        encoding="utf-8",
    )
    return repo


def test_extract_status_table_reads_readme_rows(tmp_path: Path) -> None:
    repo = _fixture_repo(tmp_path)

    table = extract_status_table(repo / "README.md")

    assert table["Riemann Hypothesis"]["main_statement"] == "Millennium.RiemannHypothesis"
    assert table["Riemann Hypothesis"]["clay_fidelity"] == "Direct"


def test_build_records_marks_external_context_only(tmp_path: Path) -> None:
    repo = _fixture_repo(tmp_path)

    records = build_records(repo)

    names = {record["name"] for record in records}
    assert "Millennium.RiemannHypothesis" in names
    rh = next(record for record in records if record["name"] == "Millennium.RiemannHypothesis")
    assert rh["external"]["problem"] == "Riemann Hypothesis"
    assert rh["external"]["context_only"] is True
    assert rh["authority"]["not_a_proof_in_current_repo"] is True


def test_millennium_problem_bridge_cli_writes_records(tmp_path: Path) -> None:
    repo = _fixture_repo(tmp_path)
    out = tmp_path / "out"

    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(repo),
            "--output-dir",
            str(out),
        ],
        cwd=REPO_ROOT,
        check=True,
    )

    rows = (out / "millennium_problem_records.jsonl").read_text(encoding="utf-8").splitlines()
    summary = json.loads((out / "millennium_problem_bridge_summary.json").read_text(encoding="utf-8"))
    assert len(rows) == 3
    assert summary["records"] == 3
    assert summary["by_problem"]["Riemann Hypothesis"] == 3

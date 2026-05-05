import json
import subprocess
import sys
from pathlib import Path

from tools.infra.aesop_tactic_prior import classify_tactic, tactic_head


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "tools" / "infra" / "aesop_tactic_prior.py"


def test_tactic_head_handles_common_prefixes() -> None:
    assert tactic_head("simp [foo]") == "simp"
    assert tactic_head("try | aesop") == "aesop"


def test_classify_tactic_uses_aesop_style_phases() -> None:
    assert classify_tactic("simp_all")["phase"] == "normalization"
    assert classify_tactic("constructor")["phase"] == "safe"
    assert classify_tactic("apply h")["phase"] == "unsafe"
    assert classify_tactic("aesop")["phase"] == "search"
    assert classify_tactic("apply h")["authority"]["lean_remains_proof_authority"] is True


def test_aesop_tactic_prior_cli_single_tactic() -> None:
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "rfl"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(result.stdout)
    assert payload["phase"] == "safe"
    assert payload["success_probability_prior"] > 0

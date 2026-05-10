from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.infra.chatgpt_lean_module_audit import build_prompt, infer_module_name

SCRIPT = Path("tools/infra/chatgpt_lean_module_audit.py")
VALID_RESPONSE = """ROLE::translator

SUMMARY::Facade proposal.

MATHLIB_ROOTING::
- keep owner import

THEOREM_STRENGTH::
- local facade only

OWNER_SHADOW_DRIFT::
- none

ASSUMPTION_PACKAGING::
- none

MINIMAL_REFACTOR_PLAN::
1. Keep export facade.

DROP_IN_REPLACEMENT::
```lean
import InfoGeometry.ExponentialFamily.Analytic.LogSumExp

namespace InfoGeometry.Canonical.LogSumExp

export InfoGeometry.Analytic (logSumExp)

end InfoGeometry.Canonical.LogSumExp
```

RISKS::
- local check required

LOCAL_VERIFICATION_REQUIRED::
- lake env lean extracted replacement

PROMOTION_ALLOWED::no
"""


def test_infer_module_name_from_lean_path() -> None:
    assert infer_module_name(Path("lean/InfoGeometry/Canonical/LogSumExp.lean")) == "InfoGeometry.Canonical.LogSumExp"


def test_build_prompt_contains_authority_membrane_and_target_code() -> None:
    prompt = build_prompt(
        module_name="InfoGeometry.Canonical.LogSumExp",
        target_file="lean/InfoGeometry/Canonical/LogSumExp.lean",
        lineage_ref="lineage_test",
        lean_source="import Mathlib\n\n#check Nat\n",
        context="owner context",
    )

    assert "PROMOTION_ALLOWED must be no" in prompt
    assert "DROP_IN_REPLACEMENT" in prompt
    assert "BEGIN_TARGET_LEAN_MODULE" in prompt
    assert "#check Nat" in prompt
    assert "BEGIN_ADDITIONAL_CONTEXT" in prompt
    assert "owner context" in prompt


def test_cli_prompt_only_writes_prompt(tmp_path: Path) -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--file",
            "lean/InfoGeometry/Canonical/LogSumExp.lean",
            "--out-dir",
            str(tmp_path),
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert Path(result["prompt"]).exists()
    assert result["target_module"] == "InfoGeometry.Canonical.LogSumExp"


def test_cli_offline_response_imports_packet_without_lean_check(tmp_path: Path) -> None:
    response = tmp_path / "response.txt"
    response.write_text(VALID_RESPONSE, encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--file",
            "lean/InfoGeometry/Canonical/LogSumExp.lean",
            "--lineage-ref",
            "lineage_test",
            "--out-dir",
            str(tmp_path / "out"),
            "--response",
            str(response),
            "--no-lean-check",
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    packet = json.loads(Path(result["packet"]).read_text(encoding="utf-8"))
    assert packet["kind"] == "ChatGPTSocraticAuditPacket"
    assert packet["promotion_allowed"] is False
    assert packet["local_lean_check"]["status"] == "not_run"
    assert Path(result["replacement"]).exists()

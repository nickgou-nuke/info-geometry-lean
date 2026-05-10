from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.infra.chatgpt_external_audit import (
    ExternalAuditError,
    ensure_proposal_only,
    extract_drop_in_replacement,
    make_packet,
)

SCRIPT = Path("tools/infra/chatgpt_external_audit.py")
VALID_RESPONSE = """ROLE::translator

SUMMARY::Facade proposal.

DROP_IN_REPLACEMENT::
```lean
import InfoGeometry.ExponentialFamily.Analytic.LogSumExp

namespace InfoGeometry.Canonical.LogSumExp

export InfoGeometry.Analytic (logSumExp)

end InfoGeometry.Canonical.LogSumExp
```

RISKS::
- local check required

PROMOTION_ALLOWED::no
"""


def test_extracts_fenced_drop_in_replacement() -> None:
    replacement = extract_drop_in_replacement(VALID_RESPONSE)

    assert replacement.startswith("import InfoGeometry.ExponentialFamily.Analytic.LogSumExp")
    assert "namespace InfoGeometry.Canonical.LogSumExp" in replacement
    assert "```" not in replacement


def test_extracts_dom_innertext_style_drop_in_replacement() -> None:
    response = """ROLE::translator
DROP_IN_REPLACEMENT::
lean
import InfoGeometry.ExponentialFamily.Analytic.LogSumExp

namespace InfoGeometry.Canonical.LogSumExp

end InfoGeometry.Canonical.LogSumExp
RISKS::
none
PROMOTION_ALLOWED::no
"""

    replacement = extract_drop_in_replacement(response)

    assert replacement.startswith("import InfoGeometry")
    assert not replacement.startswith("lean")


def test_packet_is_proposal_only_and_schema_valid(tmp_path: Path) -> None:
    packet = make_packet(
        response_text=VALID_RESPONSE,
        target_file="lean/InfoGeometry/Canonical/LogSumExp.lean",
        target_module="InfoGeometry.Canonical.LogSumExp",
        lineage_ref="lineage_test",
        transcript_ref="artifact://transcript",
        replacement_ref="artifact://replacement",
    )
    ensure_proposal_only(packet)
    assert packet["promotion_allowed"] is False
    assert packet["authority_ceiling"] == "proposal"

    packet_path = tmp_path / "packet.json"
    packet_path.write_text(json.dumps(packet), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/infra/hive_packet_validate.py", "validate", "--packet", str(packet_path)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "VALID hive packet" in proc.stdout


def test_rejects_external_promotion_claim() -> None:
    with pytest.raises(ExternalAuditError, match="PROMOTION_ALLOWED"):
        make_packet(
            response_text=VALID_RESPONSE.replace("PROMOTION_ALLOWED::no", "PROMOTION_ALLOWED::yes"),
            target_file="lean/InfoGeometry/Canonical/LogSumExp.lean",
            target_module="InfoGeometry.Canonical.LogSumExp",
            lineage_ref="lineage_test",
        )


def test_rejects_authority_packet_emission() -> None:
    packet = make_packet(
        response_text=VALID_RESPONSE,
        target_file="lean/InfoGeometry/Canonical/LogSumExp.lean",
        target_module="InfoGeometry.Canonical.LogSumExp",
        lineage_ref="lineage_test",
    )
    packet["emitted_packet_kinds"].append("LeanVerificationPacket")

    with pytest.raises(ExternalAuditError, match="authority packet"):
        ensure_proposal_only(packet)


def test_cli_parse_writes_packet_and_replacement(tmp_path: Path) -> None:
    response_path = tmp_path / "response.txt"
    response_path.write_text(VALID_RESPONSE, encoding="utf-8")
    out_dir = tmp_path / "out"

    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "parse",
            "--response",
            str(response_path),
            "--target-file",
            "lean/InfoGeometry/Canonical/LogSumExp.lean",
            "--target-module",
            "InfoGeometry.Canonical.LogSumExp",
            "--lineage-ref",
            "lineage_test",
            "--out-dir",
            str(out_dir),
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert Path(result["packet"]).exists()
    assert Path(result["replacement"]).exists()

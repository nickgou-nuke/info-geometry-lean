from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TOOL = REPO / "tools" / "lean_improver_probe.py"


def test_lean_improver_probe_ranks_non_mutating_candidates(tmp_path: Path) -> None:
    lean = tmp_path / "Sample.lean"
    lean.write_text(
        """
theorem short (p : Prop) (h : p) : p := by
  exact h

theorem longer (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  have hq : q := by
    exact hpq hp
  exact hqr hq
""".strip()
        + "\n",
        encoding="utf-8",
    )
    json_out = tmp_path / "probe.json"
    md_out = tmp_path / "probe.md"

    subprocess.run(
        [
            sys.executable,
            str(TOOL),
            str(lean),
            "--min-score",
            "2",
            "--json-out",
            str(json_out),
            "--md-out",
            str(md_out),
        ],
        check=True,
        cwd=REPO,
    )

    payload = json.loads(json_out.read_text(encoding="utf-8"))
    prompt = md_out.read_text(encoding="utf-8")

    assert payload["schema"] == "info_geometry.lean_improver_probe.v1"
    assert payload["improverCompatibility"]["mutatesLeanSource"] is False
    assert payload["candidates"][0]["name"] == "longer"
    assert "authority_class" in payload["candidates"][0]
    assert "Preserve theorem statements and names" in prompt
    assert "targeted `lake env lean <file>` gate" in prompt


def test_lean_improver_probe_distinguishes_rooted_proofs_from_sockets(tmp_path: Path) -> None:
    lean = tmp_path / "Authority.lean"
    lean.write_text(
        """
import Mathlib.Algebra.Ring.Basic

structure DemoPacket where
  carrier : Type

theorem rooted (a : Nat) : a = a := by
  exact rfl

theorem packet_socket : Nonempty DemoPacket := by
  exact ⟨{ carrier := Nat }⟩
""".strip()
        + "\n",
        encoding="utf-8",
    )
    json_out = tmp_path / "probe.json"

    subprocess.run(
        [
            sys.executable,
            str(TOOL),
            str(lean),
            "--min-score",
            "1",
            "--json-out",
            str(json_out),
        ],
        check=True,
        cwd=REPO,
    )

    payload = json.loads(json_out.read_text(encoding="utf-8"))
    by_name = {row["name"]: row for row in payload["candidates"]}

    assert by_name["rooted"]["authority_class"] == "mathlib_rooted_proof_chain"
    assert by_name["packet_socket"]["authority_class"] == "mixed_root_and_socket"
    assert any(signal.startswith("socket:") for signal in by_name["packet_socket"]["authority_signals"])

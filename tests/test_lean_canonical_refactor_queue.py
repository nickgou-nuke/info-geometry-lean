from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO = Path('/home/goutev/repos/info-geometry-lean')
TOOL = REPO / 'tools' / 'infra' / 'lean_canonical_refactor_queue.py'

def test_queue_marks_authority_classes(tmp_path: Path) -> None:
    lean = tmp_path / 'AuthorityQueue.lean'
    lean.write_text('''
import Mathlib.Algebra.Ring.Basic

structure DemoPacket where
  carrier : Type

theorem rooted_long (a : Nat) : a = a := by
  have h : a = a := by
    exact rfl
  have h01 : a = a := h
  have h02 : a = a := h01
  have h03 : a = a := h02
  have h04 : a = a := h03
  have h05 : a = a := h04
  have h06 : a = a := h05
  have h07 : a = a := h06
  have h08 : a = a := h07
  have h09 : a = a := h08
  have h10 : a = a := h09
  have h11 : a = a := h10
  have h12 : a = a := h11
  have h13 : a = a := h12
  have h14 : a = a := h13
  have h15 : a = a := h14
  have h16 : a = a := h15
  have h17 : a = a := h16
  have h18 : a = a := h17
  have h19 : a = a := h18
  have h20 : a = a := h19
  have h21 : a = a := h20
  have h22 : a = a := h21
  have h23 : a = a := h22
  have h24 : a = a := h23
  have h25 : a = a := h24
  have h26 : a = a := h25
  have h27 : a = a := h26
  have h28 : a = a := h27
  have h29 : a = a := h28
  have h30 : a = a := h29
  have h31 : a = a := h30
  have h32 : a = a := h31
  have h33 : a = a := h32
  have h34 : a = a := h33
  have h35 : a = a := h34
  have h36 : a = a := h35
  have h37 : a = a := h36
  have h38 : a = a := h37
  have h39 : a = a := h38
  have h40 : a = a := h39
  have h41 : a = a := h40
  have h42 : a = a := h41
  have h43 : a = a := h42
  exact h

theorem packet_interface_long : Nonempty DemoPacket := by
  have h : DemoPacket := { carrier := Nat }
  exact ⟨h⟩
'''.strip() + '\n', encoding='utf-8')
    out = tmp_path / 'queue.json'
    subprocess.run([sys.executable, str(TOOL), '--file', str(lean), '--json-out', str(out), '--target-limit', '10'], check=True, cwd=REPO)
    payload = json.loads(out.read_text(encoding='utf-8'))
    details = {row['name']: row for row in payload['targetDetails']}
    assert payload['closureRules'][-2].startswith('distinguish mathlib/repo-rooted')
    assert details['rooted_long']['authorityClass'] == 'mathlib_rooted_proof_chain'
    assert details['packet_interface_long']['authorityClass'] == 'mixed_root_and_interface'
    assert any(sig.startswith('interface:') for sig in details['packet_interface_long']['authoritySignals'])

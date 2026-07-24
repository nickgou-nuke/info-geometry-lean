#!/usr/bin/env python3
"""Socratic Verifier — invokes socratic_clawbot for critique and repair."""

from __future__ import annotations

import json
import subprocess
import tempfile
from pathlib import Path
from dataclasses import dataclass
from typing import Optional


@dataclass
class SocraticCritique:
    verdict: str  # "PASS" | "NEEDS_REPAIR" | "REJECT"
    critique: str
    repair_patch: Optional[str] = None
    confidence: float = 0.0


def run_socratic_critique(lean_file: Path, theorem_name: str, context: str = "") -> SocraticCritique:
    """Invoke socratic_clawbot.py for critique/repair."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        response_out = f.name
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        candidate_out = f.name
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        json_out = f.name

    try:
        # Build the theorem statement for the prompt
        prompt = f"""
Lean 4 theorem to verify/repair:

```lean4
{lean_file.read_text()}
```

Theorem: {theorem_name}

Mathematical context: {context}

Please:
1. Identify any gaps, missing imports, or incorrect tactics
2. If the proof is incomplete (`sorry`), suggest a concrete repair strategy
3. If the statement is mathematically incorrect, explain why
4. Return a JSON with: verdict, critique, repair_patch (if any), confidence
"""
        
        # Write prompt to temp file for socratic_clawbot
        with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as f:
            prompt_file = f.name
            f.write(prompt)
        
        cmd = [
            "python3", "tools/infra/socratic_clawbot.py",
            "--file", str(lean_file),
            "--theorem", theorem_name,
            "--prompt-profile", "repair",
            "--json-out", json_out,
            "--response-out", response_out,
            "--candidate-out", candidate_out,
            "--dry-run",  # Use dry-run for critique only
        ]
        
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=180, cwd=Path.cwd())
        
        if result.returncode != 0:
            return SocraticCritique(
                verdict="ERROR",
                critique=f"Socratic tool failed: {result.stderr[:500]}",
                confidence=0.0
            )
        
        # Parse the JSON output
        try:
            with open(json_out) as f:
                data = json.load(f)
            return SocraticCritique(
                verdict=data.get("verdict", "UNKNOWN"),
                critique=data.get("critique", data.get("response", "")),
                repair_patch=data.get("repair_patch"),
                confidence=float(data.get("confidence", 0.5))
            )
        except Exception as e:
            return SocraticCritique(
                verdict="PARSE_ERROR",
                critique=f"Failed to parse output: {e}",
                confidence=0.0
            )
    finally:
        # Cleanup
        for f in [response_out, candidate_out, json_out]:
            try:
                Path(f).unlink()
            except:
                pass


def apply_repair(lean_file: Path, repair_patch: str) -> bool:
    """Apply a repair patch to the Lean file."""
    try:
        # For now, just append the repair as a comment + new version
        # A real implementation would parse and apply the patch
        content = lean_file.read_text()
        backup = lean_file.with_suffix('.lean.bak')
        lean_file.write_text(content + "\n\n-- REPAIR PATCH --\n" + repair_patch)
        return True
    except Exception as e:
        print(f"Failed to apply repair: {e}")
        return False
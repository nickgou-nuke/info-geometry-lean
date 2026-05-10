from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
TOOL = REPO / "tools" / "alexandria" / "conductive_context_to_lean_skeleton.py"


def test_conductive_context_to_lean_skeleton_generates_review_packet(tmp_path: Path) -> None:
    packet = {
        "query": "J-self-adjoint projection Drazin",
        "activatedEdges": [
            {
                "kind": "debruijn_sequence",
                "conductivity": 2.1,
                "weight": 1.155,
                "overlap_symbols": ["projection", "Drazin"],
                "from": "chunk_a",
                "to": "chunk_b",
                "fromPreview": "Theorem. A J-self-adjoint projection has a Drazin inverse equal to itself.",
                "toPreview": "The spectral projector is a star projection.",
            }
        ],
    }
    src = tmp_path / "context.json"
    src.write_text(json.dumps(packet), encoding="utf-8")
    out = tmp_path / "out"

    subprocess.run(
        [sys.executable, str(TOOL), "--input", str(src), "--output-dir", str(out), "--limit", "1"],
        check=True,
        cwd=REPO,
    )

    lean = (out / "conductive_skeleton.lean").read_text(encoding="utf-8")
    md = (out / "conductive_skeleton.md").read_text(encoding="utf-8")
    mapping = json.loads((out / "conductive_skeleton_map.json").read_text(encoding="utf-8"))

    assert "IsJProjection.isDrazinInverse_self hP" in lean
    assert "Conductive path selected the repo-native Krein/J-projection bridge" in lean
    assert "Ancestry hash" in lean
    assert "Conductive Context Lean Skeleton Packet" in md
    assert "ancestry hash" in md
    assert mapping["candidates"][0]["entities"]
    assert mapping["candidates"][0]["ancestry_hash"]
    assert mapping["candidates"][0]["ancestry_sources"] == ["chunk_a", "chunk_b"]

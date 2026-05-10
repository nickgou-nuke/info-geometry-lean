from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
TOOL = REPO / "tools" / "alexandria" / "proof_synthesis_report.py"


def test_proof_synthesis_report_renders_authority_bounded_prompt(tmp_path: Path) -> None:
    discovery = [
        {
            "seed": "scc_krein_projection",
            "depth": 1,
            "conductiveWeight": 2.1,
            "path": ["scc_krein_projection", "scc_drazin_projector"],
            "pathTerms": ["Krein space", "J-self-adjoint", "Drazin inverse", "Moore-Penrose"],
            "witnesses": [
                {
                    "scc": "scc_krein_projection",
                    "chunk": "chunk_a",
                    "preview": "Theorem. A J-self-adjoint projection has a Drazin inverse equal to itself.",
                    "terms": ["J-self-adjoint", "projection"],
                }
            ],
        }
    ]
    src = tmp_path / "discovery.json"
    src.write_text(json.dumps(discovery), encoding="utf-8")
    json_out = tmp_path / "packet.json"
    md_out = tmp_path / "prompt.md"

    subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--input-json",
            str(src),
            "--query",
            "Krein Moore-Penrose Drazin projector",
            "--json-out",
            str(json_out),
            "--md-out",
            str(md_out),
        ],
        check=True,
        cwd=REPO,
    )

    packet = json.loads(json_out.read_text(encoding="utf-8"))
    prompt = md_out.read_text(encoding="utf-8")

    assert packet["topPath"]["path"] == ["scc_krein_projection", "scc_drazin_projector"]
    assert "Proof Synthesis Report Prompt" in prompt
    assert "Lean is proof authority" in prompt
    assert "Graph witnesses are language/context/provenance only" in prompt
    assert "J-self-adjointness in a Krein metric is not Hilbert self-adjointness" in prompt
    assert "InfoGeometry.Krein.KreinSpace.IsJProjection.isDrazinInverse_self" in prompt
    assert "rightProjector_eq_range_starProjection" in prompt
    assert "`scc_krein_projection` / `chunk_a`" in prompt

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TOOL = REPO / "tools" / "infra" / "generate_truth_transport.py"


def test_generate_truth_transport_from_run_artifact(tmp_path: Path) -> None:
    packet_path = tmp_path / "packet.json"
    packet_path.write_text(
        json.dumps(
            {
                "packet_id": "packet-1",
                "research_goal": "transport graph truth",
                "formalization_targets": [{"name": "InfoGeometry.Transport.target"}],
            }
        ),
        encoding="utf-8",
    )
    gravity_path = tmp_path / "gravity.json"
    gravity_path.write_text(
        json.dumps(
            {
                "graph_source": "jsonl",
                "node_count": 1,
                "edge_count": 0,
                "items": [
                    {
                        "id": "InfoGeometry.Transport.neighbor",
                        "name": "InfoGeometry.Transport.neighbor",
                        "module": "InfoGeometry.Transport",
                        "decl_kind": "theorem",
                        "score": 3.0,
                        "distance": 0,
                        "source_excerpt": {
                            "path": "lean/InfoGeometry/Transport.lean",
                            "line": 4,
                            "lines": [{"line": 4, "text": "theorem neighbor : True := by"}],
                        },
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    run_path = tmp_path / "run.json"
    run_path.write_text(
        json.dumps(
            {
                "run_id": "run-1",
                "packet_id": "packet-1",
                "packet_path": str(packet_path),
                "planner_text": "ROUTE: deepseek_proof\nEXECUTION_ALLOWED: no\nNEXT_ACTION: inspect\nRATIONALE: bounded\nGUARDS: gate",
                "gravity": {"context_path": str(gravity_path)},
            }
        ),
        encoding="utf-8",
    )
    out_path = tmp_path / "transport.json"

    subprocess.run(
        [sys.executable, str(TOOL), "--run", str(run_path), "--out", str(out_path)],
        cwd=REPO,
        check=True,
        text=True,
        capture_output=True,
    )
    packet = json.loads(out_path.read_text(encoding="utf-8"))

    assert packet["schema"] == "info_geometry.truth_transport.v1"
    assert packet["packet_id"] == "packet-1"
    assert packet["planner_route"]["route"] == "deepseek_proof"
    assert packet["gravity_context"]["items"][0]["id"] == "InfoGeometry.Transport.neighbor"

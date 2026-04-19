from pathlib import Path

from tools.infra.hermes_bounded_runner import Packet, build_truth_transport_packet, extract_text, parse_planner_route


def test_extract_text_recovers_reasoning_route_block_when_content_empty():
    response = {
        "choices": [
            {
                "message": {
                    "content": "",
                    "reasoning_content": (
                        "analysis before answer\n"
                        "ROUTE: deepseek_proof\n"
                        "EXECUTION_ALLOWED: no\n"
                        "NEXT_ACTION: inspect graph-grounded Lean corridor\n"
                        "RATIONALE: The target has source-backed neighbors. No mutation is needed.\n"
                        "GUARDS: [\"lake build\", \"clawcode gate\"]\n"
                    ),
                }
            }
        ]
    }

    assert extract_text(response).startswith("ROUTE: deepseek_proof")
    assert "EXECUTION_ALLOWED: no" in extract_text(response)


def test_truth_transport_packet_carries_graph_context_and_gates():
    planner_text = "\n".join(
        [
            "ROUTE: deepseek_proof",
            "EXECUTION_ALLOWED: no",
            "NEXT_ACTION: inspect local proof corridor",
            "RATIONALE: Graph context is source-backed.",
            "GUARDS: requires_clawcode_gate",
        ]
    )
    packet = Packet(
        path=Path("quarantine/hermes_memory/research_packets/example.json"),
        data={
            "packet_id": "example",
            "research_goal": "prove source-backed theorem",
            "formalization_targets": [{"name": "InfoGeometry.Example.target"}],
        },
    )
    gravity_context = {
        "graph_source": "jsonl",
        "node_count": 2,
        "edge_count": 1,
        "items": [
            {
                "id": "InfoGeometry.Example.neighbor",
                "name": "InfoGeometry.Example.neighbor",
                "module": "InfoGeometry.Example",
                "decl_kind": "theorem",
                "score": 7.0,
                "distance": 0,
                "source_excerpt": {
                    "path": "lean/InfoGeometry/Example.lean",
                    "line": 10,
                    "start": 10,
                    "end": 12,
                    "lines": [{"line": 10, "text": "theorem neighbor : True := by"}],
                },
            }
        ],
    }

    transport = build_truth_transport_packet(
        run_id="run",
        packet=packet,
        planner_text=planner_text,
        gravity_context=gravity_context,
        gravity_path=Path("artifacts/gravity/run.json"),
    )

    assert parse_planner_route(planner_text)["route"] == "deepseek_proof"
    assert transport["schema"] == "info_geometry.truth_transport.v1"
    assert transport["handoff_policy"]["codex_mutation_allowed"] is False
    assert transport["gravity_context"]["items"][0]["id"] == "InfoGeometry.Example.neighbor"

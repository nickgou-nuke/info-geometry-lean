from __future__ import annotations

import json
import threading
import urllib.request
from http.server import ThreadingHTTPServer
from pathlib import Path

from leantrail.api.server import LeanTrailRequestHandler
from leantrail.backend.models import GraphSnapshot
from leantrail.backend.query_api import LeanTrailQueryAPI
from leantrail.backend.store import GraphStore


def _snapshot_with_cone_geometry() -> GraphSnapshot:
    payload = {
        "metadata": {"created_at": "test", "commit_sha": "test", "toolchain": "test", "artifact_version": 1},
        "nodes": [
            {
                "id": "Cone.Rich",
                "name": "Cone.Rich",
                "kind": "Declaration",
                "module": "InfoGeometry.Cone",
                "file": "InfoGeometry/Cone.lean",
                "line": 10,
                "rep_depth": None,
                "role": "owner",
                "module_family": "InfoGeometry",
                "commit_sha": "test",
                "toolchain": "test",
                "artifact_version": 1,
                "attrs": {
                    "lawful_cone": {
                        "leg_count": 3,
                        "shared_comparison_count": 2,
                        "defect_count": 1,
                        "total_defect_cost": 4,
                        "leg_kinds": ["translator", "coherence"],
                    },
                    "lawful_path_summary": {
                        "count": 2,
                        "defectful_count": 1,
                        "max_defect_cost": 4,
                    },
                },
            },
            {
                "id": "Cone.Light",
                "name": "Cone.Light",
                "kind": "Declaration",
                "module": "InfoGeometry.Cone",
                "file": "InfoGeometry/Cone.lean",
                "line": 20,
                "rep_depth": None,
                "role": "translator",
                "module_family": "InfoGeometry",
                "commit_sha": "test",
                "toolchain": "test",
                "artifact_version": 1,
                "attrs": {
                    "lawful_cone": {
                        "leg_count": 1,
                        "shared_comparison_count": 0,
                        "defect_count": 0,
                        "total_defect_cost": 0,
                        "leg_kinds": ["translator"],
                    },
                    "lawful_path_summary": {
                        "count": 1,
                        "defectful_count": 0,
                        "max_defect_cost": 0,
                    },
                },
            },
            {
                "id": "Cone.None",
                "name": "Cone.None",
                "kind": "Declaration",
                "module": "InfoGeometry.Cone",
                "file": "InfoGeometry/Cone.lean",
                "line": 30,
                "rep_depth": None,
                "role": "owner",
                "module_family": "InfoGeometry",
                "commit_sha": "test",
                "toolchain": "test",
                "artifact_version": 1,
                "attrs": {},
            },
        ],
        "edges": [],
    }
    return GraphSnapshot.from_dict(payload)


def _api_with_store(tmp_path: Path) -> LeanTrailQueryAPI:
    api = LeanTrailQueryAPI(
        repo_root=tmp_path,
        snapshot_path=tmp_path / "graph_snapshot.json",
        bridge_dir=tmp_path / "bridge",
        bridge_schema_path=tmp_path / "bridge.schema.json",
    )
    api.store = GraphStore(_snapshot_with_cone_geometry())
    return api


def test_cone_hotspots_rank_and_filter(tmp_path: Path) -> None:
    api = _api_with_store(tmp_path)

    result = api.cone_hotspots(limit=5, min_score=2.0)

    assert result["weights"] == {"alpha": 1.0, "beta": 1.5, "gamma": 3.0}
    assert [row["node"]["name"] for row in result["hotspots"]] == ["Cone.Rich", "Cone.Light"]
    assert result["hotspots"][0]["cone_score"] > result["hotspots"][1]["cone_score"]
    assert result["hotspots"][0]["components"] == {
        "coverage": 5.0,
        "comparison_pressure": 2.0,
        "defect_pressure": 10.0,
    }
    assert result["hotspots"][0]["cone"]["leg_kinds"] == ["translator", "coherence"]


def test_cone_hotspots_http_route(tmp_path: Path) -> None:
    api = _api_with_store(tmp_path)
    LeanTrailRequestHandler.api = api
    server = ThreadingHTTPServer(("127.0.0.1", 0), LeanTrailRequestHandler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        url = f"http://127.0.0.1:{server.server_address[1]}/cone/hotspots?limit=1&min_score=1.0"
        with urllib.request.urlopen(url, timeout=5) as response:
            payload = json.loads(response.read().decode("utf-8"))
        assert payload["hotspots"][0]["node"]["name"] == "Cone.Rich"
        assert payload["hotspots"][0]["paths"]["count"] == 2
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)

from __future__ import annotations

import json
import os
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[2]
GRAPH_RAG = REPO / "tools" / "infra" / "graph_rag_query.py"
ASK_REPO = REPO / "tools" / "infra" / "ask_repo.py"


class _MockAlexandriaServer:
    def __init__(self, rows: list[dict[str, Any]]) -> None:
        self.rows = rows
        self.requests: list[dict[str, Any]] = []
        outer = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, format: str, *args: object) -> None:  # noqa: A003
                return

            def do_POST(self) -> None:  # noqa: N802
                length = int(self.headers.get("Content-Length", "0"))
                body = json.loads(self.rfile.read(length).decode("utf-8")) if length else {}
                outer.requests.append({"path": self.path, "body": body})
                payload = {
                    "error": False,
                    "hasMore": False,
                    "extra": {"warnings": []},
                    "result": outer.rows,
                }
                raw = json.dumps(payload).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(raw)))
                self.end_headers()
                self.wfile.write(raw)

        self._server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.endpoint = f"http://127.0.0.1:{self._server.server_port}"
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)

    def __enter__(self) -> "_MockAlexandriaServer":
        self._thread.start()
        return self

    def __exit__(self, *_: object) -> None:
        self._server.shutdown()
        self._server.server_close()


def _sample_rows() -> list[dict[str, Any]]:
    return [
        {
            "chunk": {
                "_key": "chk_oct_1",
                "_id": "alexandria_chunks/chk_oct_1",
                "documentKey": "doc_oct_1",
                "chunkKind": "theorem",
                "title": "Albert Vector Split Octonions G2",
                "text": "The automorphism group of the split octonions is the split real form of G2 acting on Albert vectors.",
                "tokens": ["albert", "vector", "split", "octonions", "g2"],
                "provenance": {
                    "path": "/corpus/Dray-GeometryOctonions.pdf",
                    "contentHash": "octhash1234",
                    "pageStart": 14,
                    "pageEnd": 15,
                    "section": "3. Split Octonions",
                },
            },
            "document": {
                "_key": "doc_oct_1",
                "title": "Geometry of the Octonions",
                "path": "/corpus/Dray-GeometryOctonions.pdf",
                "contentHash": "octhash1234",
            },
            "score": 9.1,
            "entities": [{"_key": "ent_g2", "entityType": "concept", "surface": "G2", "normalized": "g2"}],
            "adjNeighbors": [],
            "dagNeighbors": [
                {
                    "_key": "chk_oct_2",
                    "_id": "alexandria_chunks/chk_oct_2",
                    "chunkKind": "proof",
                    "title": "Proof of G2 invariance",
                    "edgeType": "proof_proves_theorem",
                    "direction": "inbound",
                }
            ],
        }
    ]


def test_graph_rag_alexandria_scope_ignores_poisoned_8530_and_skips_gravity(tmp_path: Path) -> None:
    lean_records = tmp_path / "lean_records.jsonl"
    lean_records.write_text(
        json.dumps(
            {
                "name": "InfoGeometry.Octonions.splitG2",
                "kind": "theorem",
                "module": "InfoGeometry.Octonions",
                "file": "lean/InfoGeometry/Octonions.lean",
                "line": 12,
                "doc": "Split octonion G2 symmetry theorem.",
                "searchTokens": ["split", "octonions", "g2"],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    with _MockAlexandriaServer(_sample_rows()) as srv:
        env = os.environ.copy()
        env["ARANGO_ENDPOINT"] = "http://127.0.0.1:8530"
        env["ARANGO_DATABASE"] = "infogeometry"
        env["ALEXANDRIA_ARANGO_ENDPOINT"] = srv.endpoint
        env["ALEXANDRIA_ARANGO_DB"] = "alexandria_unit_test"
        env["ALEXANDRIA_ARANGO_USERNAME"] = "root"
        env["ALEXANDRIA_ARANGO_PASSWORD"] = "secret"

        # Even WITHOUT --no-gravity, --scope alexandria MUST NOT run gravity (:8530)
        proc = subprocess.run(
            [
                sys.executable,
                str(GRAPH_RAG),
                "Albert Vector split octonions G2",
                "--scope",
                "alexandria",
                "--format",
                "json",
            ],
            cwd=REPO,
            env=env,
            capture_output=True,
            text=True,
            check=True,
        )
        payload = json.loads(proc.stdout)
        assert payload["scope"] == "alexandria"
        assert payload["gravity"] is None
        assert payload["lean"] == []
        assert payload["docs"] == []
        assert payload["external"] == []
        assert payload["authority"] == "retrieval_context_only"
        assert payload["authorities"]["alexandria"] == "retrieval_context_only"
        assert len(payload["alexandria"]) == 1
        alex_hit = payload["alexandria"][0]
        assert alex_hit["source"] == "alexandria"
        assert alex_hit["metadata"]["authority"] == "retrieval_context_only"
        assert alex_hit["metadata"]["documentKey"] == "doc_oct_1"
        assert alex_hit["metadata"]["pageStart"] == 14

        # Markdown output marks retrieval_context_only
        proc_md = subprocess.run(
            [
                sys.executable,
                str(GRAPH_RAG),
                "Albert Vector split octonions G2",
                "--scope",
                "alexandria",
                "--format",
                "md",
            ],
            cwd=REPO,
            env=env,
            capture_output=True,
            text=True,
            check=True,
        )
        assert "Alexandria PDFs" in proc_md.stdout
        assert "retrieval_context_only" in proc_md.stdout
        assert "not verified Lean proof evidence" in proc_md.stdout

        # Combined scope lean,alexandria
        proc_combo = subprocess.run(
            [
                sys.executable,
                str(GRAPH_RAG),
                "split octonions G2",
                "--scope",
                "lean,alexandria",
                "--lean-records",
                str(lean_records),
                "--no-gravity",
                "--format",
                "json",
            ],
            cwd=REPO,
            env=env,
            capture_output=True,
            text=True,
            check=True,
        )
        combo = json.loads(proc_combo.stdout)
        assert combo["lean"] and combo["alexandria"]
        assert "authority" not in combo  # lean is present; per-source authorities apply
        assert combo["authorities"]["alexandria"] == "retrieval_context_only"

        # ask_repo.py --brief and --answer with --scope alexandria
        for flag in ("--brief", "--answer"):
            ask_proc = subprocess.run(
                [sys.executable, str(ASK_REPO), "split octonions G2", "--scope", "alexandria", flag],
                cwd=REPO,
                env=env,
                capture_output=True,
                text=True,
                check=True,
            )
            low = ask_proc.stdout.lower()
            assert "octonions" in low or "albert" in low
            assert "retrieval_context_only" in low
            assert "not verified lean proof evidence" in low
            assert "no ranked hits were found" not in low


def test_graph_rag_and_ask_repo_reject_invalid_scope_and_forbidden_target() -> None:
    for script in (GRAPH_RAG, ASK_REPO):
        bad_scope = subprocess.run(
            [sys.executable, str(script), "Clifford", "--scope", "bogus_scope"],
            cwd=REPO,
            capture_output=True,
            text=True,
        )
        assert bad_scope.returncode == 2

    bad_ep = subprocess.run(
        [
            sys.executable,
            str(GRAPH_RAG),
            "Clifford",
            "--scope",
            "alexandria",
            "--alexandria-endpoint",
            "http://127.0.0.1:8530",
        ],
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    assert bad_ep.returncode == 2

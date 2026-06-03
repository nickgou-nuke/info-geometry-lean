from __future__ import annotations

import argparse
import json
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, unquote, urlparse

from leantrail.backend.query_api import LeanTrailQueryAPI


def _bool_query(value: str | None, default: bool = True) -> bool:
    if value is None:
        return default
    return value.lower() in {"1", "true", "yes", "on"}


class LeanTrailRequestHandler(BaseHTTPRequestHandler):
    api: LeanTrailQueryAPI

    def _write_json(self, payload: dict[str, Any], status: HTTPStatus = HTTPStatus.OK) -> None:
        body = json.dumps(payload, ensure_ascii=True).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:  # noqa: N802
        parsed = urlparse(self.path)
        query = parse_qs(parsed.query)
        path = parsed.path

        try:
            if path in {"/health", "/healthz"}:
                self._write_json({"ok": True})
                return

            if path == "/api/v1/meta":
                self._write_json(
                    {
                        "service": "leantrail",
                        "version": "0.2",
                        "endpoints": [
                            "GET /search?q=...",
                            "GET /decl/{name}",
                            "GET /neighborhood/{name}?radius=2",
                            "GET /dedup/candidates?status=active&limit=50",
                            "GET /path?from=...&to=...&lawful_only=true&state_policy=any",
                            "GET /proofstate?file=...&line=...&col=...",
                            "GET /coherence/hotspots",
                            "GET /holonomy/hotspots",
                            "POST /bridge-candidate",
                        ],
                        "aliases": [
                            "/api/v1/search",
                            "/api/v1/decl/{name}",
                            "/api/v1/neighborhood/{name}",
                            "/api/v1/dedup/candidates",
                            "/api/v1/path",
                            "/api/v1/proofstate",
                            "/api/v1/coherence/hotspots",
                            "/api/v1/holonomy/hotspots",
                            "/api/v1/bridge-candidate",
                        ],
                    }
                )
                return

            if path in {"/search", "/api/v1/search"}:
                q = (query.get("q") or [""])[0]
                limit = int((query.get("limit") or ["50"])[0])
                self._write_json(self.api.search(q, limit=limit))
                return

            if path in {"/dedup/candidates", "/api/v1/dedup/candidates"}:
                status = (query.get("status") or ["active"])[0]
                limit = int((query.get("limit") or ["50"])[0])
                self._write_json(self.api.dedup_candidates(status=status, limit=limit))
                return

            if path.startswith("/decl/") or path.startswith("/api/v1/decl/"):
                prefix = "/decl/" if path.startswith("/decl/") else "/api/v1/decl/"
                name = unquote(path[len(prefix) :])
                result = self.api.decl(name)
                status = HTTPStatus.OK if result.get("found") else HTTPStatus.NOT_FOUND
                self._write_json(result, status=status)
                return

            if path.startswith("/neighborhood/") or path.startswith("/api/v1/neighborhood/"):
                prefix = "/neighborhood/" if path.startswith("/neighborhood/") else "/api/v1/neighborhood/"
                name = unquote(path[len(prefix) :])
                radius = int((query.get("radius") or ["2"])[0])
                self._write_json(self.api.neighborhood(name, radius=radius))
                return

            if path in {"/path", "/api/v1/path"}:
                src = (query.get("from") or [""])[0]
                dst = (query.get("to") or [""])[0]
                lawful_only = _bool_query((query.get("lawful_only") or ["true"])[0], default=True)
                state_policy = (query.get("state_policy") or ["any"])[0]
                self._write_json(
                    self.api.path(
                        src=src,
                        dst=dst,
                        lawful_only=lawful_only,
                        state_policy=state_policy,
                    )
                )
                return

            if path in {"/proofstate", "/api/v1/proofstate"}:
                file = (query.get("file") or [""])[0]
                line = int((query.get("line") or ["1"])[0])
                col = int((query.get("col") or query.get("character") or ["1"])[0])
                self._write_json(self.api.proofstate(file=file, line=line, col=col))
                return

            if path in {"/coherence/hotspots", "/api/v1/coherence/hotspots"}:
                limit = int((query.get("limit") or ["25"])[0])
                self._write_json(self.api.coherence_hotspots(limit=limit))
                return

            if path in {"/holonomy/hotspots", "/api/v1/holonomy/hotspots"}:
                limit = int((query.get("limit") or ["25"])[0])
                alpha = float((query.get("alpha") or ["1.5"])[0])
                beta = float((query.get("beta") or ["2.0"])[0])
                gamma = float((query.get("gamma") or ["3.0"])[0])
                min_score = float((query.get("min_score") or ["0.0"])[0])
                self._write_json(
                    self.api.holonomy_hotspots(
                        limit=limit,
                        alpha=alpha,
                        beta=beta,
                        gamma=gamma,
                        min_score=min_score,
                    )
                )
                return

            self._write_json({"error": f"unknown endpoint: {path}"}, status=HTTPStatus.NOT_FOUND)
        except ValueError as exc:
            self._write_json({"error": str(exc)}, status=HTTPStatus.BAD_REQUEST)
        except Exception as exc:  # pragma: no cover
            self._write_json({"error": str(exc)}, status=HTTPStatus.INTERNAL_SERVER_ERROR)

    def do_POST(self) -> None:  # noqa: N802
        parsed = urlparse(self.path)
        if parsed.path not in {"/bridge-candidate", "/api/v1/bridge-candidate"}:
            self._write_json({"error": f"unknown endpoint: {parsed.path}"}, status=HTTPStatus.NOT_FOUND)
            return

        try:
            content_len = int(self.headers.get("Content-Length", "0"))
            raw = self.rfile.read(content_len)
            payload = json.loads(raw.decode("utf-8")) if raw else {}
            result = self.api.create_bridge_candidate(payload)
            self._write_json(result, status=HTTPStatus.CREATED)
        except json.JSONDecodeError as exc:
            self._write_json({"error": f"invalid JSON: {exc}"}, status=HTTPStatus.BAD_REQUEST)
        except ValueError as exc:
            self._write_json({"error": str(exc)}, status=HTTPStatus.BAD_REQUEST)
        except Exception as exc:  # pragma: no cover
            self._write_json({"error": str(exc)}, status=HTTPStatus.INTERNAL_SERVER_ERROR)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="LeanTrail query API server.")
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--snapshot", default="artifacts/leantrail/graph_snapshot.json")
    parser.add_argument(
        "--bridge-dir",
        default="artifacts/dag/process-flow/bridge-candidates",
        help="Destination directory for emitted bridge candidate packets.",
    )
    parser.add_argument(
        "--bridge-schema",
        default="leantrail/schemas/leantrail_bridge_request.schema.json",
        help="Schema for POST /bridge-candidate payload validation.",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    repo_root = Path(args.repo_root).resolve()
    snapshot_path = (repo_root / args.snapshot).resolve() if not Path(args.snapshot).is_absolute() else Path(args.snapshot)
    bridge_dir = (repo_root / args.bridge_dir).resolve() if not Path(args.bridge_dir).is_absolute() else Path(args.bridge_dir)
    bridge_schema = (
        (repo_root / args.bridge_schema).resolve() if not Path(args.bridge_schema).is_absolute() else Path(args.bridge_schema)
    )

    api = LeanTrailQueryAPI(
        repo_root=repo_root,
        snapshot_path=snapshot_path,
        bridge_dir=bridge_dir,
        bridge_schema_path=bridge_schema,
    )
    api.ensure_loaded()

    LeanTrailRequestHandler.api = api
    server = ThreadingHTTPServer((args.host, args.port), LeanTrailRequestHandler)
    print(f"LeanTrail API listening at http://{args.host}:{args.port}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

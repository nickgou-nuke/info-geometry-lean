import json
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

from tools.infra.check_resident_model_endpoint import run_check


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):  # noqa: N802
        if self.path == "/v1/models":
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(json.dumps({"data": [{"id": "leanstral-gguf"}]}).encode())
        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self):  # noqa: N802
        if self.path == "/v1/chat/completions":
            _ = self.rfile.read(int(self.headers.get("Content-Length", "0")))
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(json.dumps({"choices": [{"message": {"content": "ok"}}]}).encode())
        else:
            self.send_response(404)
            self.end_headers()

    def log_message(self, *_args):
        return


def start_server():
    server = HTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    return server


def test_run_check_passes_against_mock_endpoint(tmp_path: Path) -> None:
    server = start_server()
    hermes = tmp_path / "hermes.yaml"
    nemoclaw = tmp_path / "nemoclaw.yaml"
    hermes.write_text("model:\n  default: leanstral-gguf\n", encoding="utf-8")
    nemoclaw.write_text(
        "lanes:\n"
        "  planner_engine:\n"
        "    model: \"leanstral-gguf\"\n"
        "  logic_engine:\n"
        "    model: \"leanstral-gguf\"\n",
        encoding="utf-8",
    )

    try:
        report = run_check(
            base_url=f"http://127.0.0.1:{server.server_port}/v1",
            expected_model="leanstral-gguf",
            timeout=3,
            hermes_config=hermes,
            nemoclaw_config=nemoclaw,
            probe_chat=True,
        )
    finally:
        server.shutdown()

    assert report["ok"] is True
    assert report["models"]["expected_present"] is True
    assert report["chat_probe"]["ok"] is True
    assert report["config"]["hermes_default_matches"] is True


def test_run_check_detects_config_mismatch(tmp_path: Path) -> None:
    server = start_server()
    hermes = tmp_path / "hermes.yaml"
    hermes.write_text("model:\n  default: other-model\n", encoding="utf-8")

    try:
        report = run_check(
            base_url=f"http://127.0.0.1:{server.server_port}/v1",
            expected_model="leanstral-gguf",
            timeout=3,
            hermes_config=hermes,
            nemoclaw_config=None,
            probe_chat=False,
        )
    finally:
        server.shutdown()

    assert report["ok"] is False
    assert report["config"]["hermes_default_matches"] is False

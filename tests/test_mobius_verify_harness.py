from __future__ import annotations

import csv
import importlib.util
import json
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = REPO_ROOT / "tools" / "mobius" / "verify_harness.py"


@pytest.fixture()
def harness_module():
    spec = importlib.util.spec_from_file_location("mobius_verify_harness", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise AssertionError(f"Unable to load module spec for {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _write_packet(path: Path, *, classification: str = "parabolic") -> Path:
    packet = {
        "schema_version": "1.0",
        "description": "test packet",
        "matrix": {"a": "1", "b": "1", "c": "0", "d": "1"},
        "ring": "QQ",
        "expected": {
            "determinant": "1",
            "trace": "2",
            "sigma": "4",
            "classification": classification,
            "fixed_points": ["infinity"],
            "projective_eigendirections": ["infinity"],
        },
    }
    path.write_text(json.dumps(packet), encoding="utf-8")
    return path


def test_default_packet_paths_discovers_builtin_packets(harness_module):
    paths = harness_module.default_packet_paths(REPO_ROOT)
    names = [path.name for path in paths]
    assert names == sorted(names)
    assert "mobius_packet_parabolic.json" in names
    assert "mobius_packet_hyperbolic.json" in names


def test_build_lean_driver_mentions_expected_sigma_and_classification(harness_module, tmp_path):
    packet_path = _write_packet(tmp_path / "packet.json", classification="parabolic")
    packet = harness_module.load_packet(packet_path)

    driver = harness_module.build_lean_driver(packet)

    assert "InfoGeometry.MoebiusHurwitz" in driver
    assert "classifyMoebius" in driver
    assert "MoebiusClassification.parabolic" in driver
    assert "(4 : ℝ)" in driver


def test_run_harness_writes_json_and_csv_reports(harness_module, tmp_path):
    packet_path = _write_packet(tmp_path / "packet.json")
    output_dir = tmp_path / "out"

    def fake_runner(engine, packet, root):
        assert packet.expected_classification == "parabolic"
        return harness_module.EngineResult(
            status="OK",
            classification=packet.expected_classification,
            details=f"{engine.name} accepted {packet.name}",
        )

    summary = harness_module.run_harness(
        packet_paths=[packet_path],
        output_dir=output_dir,
        engine_names=["sympy", "lean"],
        root=REPO_ROOT,
        runner=fake_runner,
    )

    assert summary["passed"] == 2
    assert summary["failed"] == 0
    assert summary["total"] == 2

    json_report = output_dir / "verify_harness_summary.json"
    csv_report = output_dir / "verify_harness_summary.csv"
    assert json_report.exists()
    assert csv_report.exists()

    payload = json.loads(json_report.read_text(encoding="utf-8"))
    assert payload["summary"] == {"passed": 2, "failed": 0, "skipped": 0, "total": 2}
    assert payload["rows"][0]["packet"] == "packet"
    assert payload["rows"][0]["engine"] == "sympy"
    assert payload["rows"][1]["engine"] == "lean"

    with csv_report.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    assert [row["engine"] for row in rows] == ["sympy", "lean"]
    assert all(row["status"] == "OK" for row in rows)

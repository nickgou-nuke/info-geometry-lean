import importlib
import sys
import types


def test_current_gpu_memory_snapshot_handles_na_values(monkeypatch) -> None:
    sys.modules.setdefault("jsonschema", types.SimpleNamespace())
    injection_common = importlib.import_module("tools.infra.injection_common")

    def fake_run_version_cmd(_cmd, _root):
        return {
            "exit": 0,
            "stdout": "0, [N/A], 1200, [N/A]\n",
        }

    monkeypatch.setattr(injection_common, "_run_version_cmd", fake_run_version_cmd)

    snapshot = injection_common.current_gpu_memory_snapshot()

    assert snapshot["available"] is True
    assert snapshot["gpus"][0]["index"] == 0
    assert snapshot["gpus"][0]["memory_total_mb"] is None
    assert snapshot["gpus"][0]["memory_used_mb"] == 1200
    assert snapshot["gpus"][0]["memory_free_mb"] is None

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from types import ModuleType
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]

JsonObj = dict[str, Any]


def _load_gate_module() -> ModuleType:
    module_path = REPO_ROOT / "tools" / "check_vacuity_policy.py"
    spec = importlib.util.spec_from_file_location("check_vacuity_policy", module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Unable to load check_vacuity_policy module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


gate = _load_gate_module()


class CheckVacuityPolicyTests(unittest.TestCase):
    def _write_report(self, entries: list[JsonObj]) -> Path:
        temp_dir = tempfile.mkdtemp(prefix="vacuity-policy-test-")
        report_path = Path(temp_dir) / "report.json"
        with open(report_path, "w", encoding="utf-8") as f:
            json.dump(entries, f)
        return report_path

    def _check(self, entries: list[JsonObj], *, validate_consistency: bool = True) -> int:
        path = self._write_report(entries)
        return gate.check_policy(
            path,
            strict_paths=list(gate.STRICT_PATHS_DEFAULT),
            bridge_hints=list(gate.BRIDGE_HINTS_DEFAULT),
            verbose=False,
            validate_consistency=validate_consistency,
        )

    def test_warning_only_passes(self):
        entries = [
            {
                "name": "A",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "violations": [{"level": "warning", "code": "V0/syntactic-vacuity"}],
            }
        ]
        rc = self._check(entries)
        self.assertEqual(rc, 0)

    def test_error_level_fails(self):
        entries = [
            {
                "name": "Dead",
                "file": "lean/InfoGeometry/Canonical/Dead.lean",
                "violations": [{"level": "error", "code": "V2/dead-public-theorem"}],
            }
        ]
        rc = self._check(entries)
        self.assertEqual(rc, 1)

    def test_consistency_mismatch_fails(self):
        # V2 in a strict file should be error, not warning.
        entries = [
            {
                "name": "Dead",
                "file": "lean/InfoGeometry/Canonical/Dead.lean",
                "violations": [{"level": "warning", "code": "V2/dead-public-theorem"}],
            }
        ]
        rc = self._check(entries)
        self.assertEqual(rc, 3)

    def test_consistency_check_can_be_skipped(self):
        entries = [
            {
                "name": "Dead",
                "file": "lean/InfoGeometry/Canonical/Dead.lean",
                "violations": [{"level": "warning", "code": "V2/dead-public-theorem"}],
            }
        ]
        rc = self._check(entries, validate_consistency=False)
        self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()

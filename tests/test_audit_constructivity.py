import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path
from types import ModuleType


REPO_ROOT = Path(__file__).resolve().parents[1]


def _load_audit_module() -> ModuleType:
    module_path = REPO_ROOT / "tools" / "quality" / "audit_constructivity.py"
    spec = importlib.util.spec_from_file_location("audit_constructivity", module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Unable to load audit_constructivity module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


audit_constructivity = _load_audit_module()


class AuditConstructivityTests(unittest.TestCase):
    def test_scan_file_ignores_strings_and_quoted_identifiers(self):
        source = """
/-- mentions sorry in prose -/
def trustCode : String := "trust.sorry"

def parserToken := ``Lean.Parser.Term.«sorry»

def reviewNote : String := "admit"
"""
        with tempfile.TemporaryDirectory(dir=REPO_ROOT, prefix="audit-constructivity-") as temp_dir:
            path = Path(temp_dir) / "Sample.lean"
            path.write_text(source, encoding="utf-8")
            findings = audit_constructivity.scan_file(path)
        self.assertFalse(any(f.category == "proof-hole" for f in findings), findings)

    def test_scan_file_reports_real_sorry(self):
        source = """
theorem real_gap : True := by
  sorry
"""
        with tempfile.TemporaryDirectory(dir=REPO_ROOT, prefix="audit-constructivity-") as temp_dir:
            path = Path(temp_dir) / "Sample.lean"
            path.write_text(source, encoding="utf-8")
            findings = audit_constructivity.scan_file(path)
        self.assertTrue(any(f.category == "proof-hole" for f in findings), findings)


if __name__ == "__main__":
    unittest.main()

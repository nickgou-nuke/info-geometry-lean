"""
Regression test suite for Lean-side audit architecture and pipeline hygiene.

Verifies:
1. AuditStrict.lean does NOT import AuditNative or InfoGeometry.AllExhaustive (prevents the 19,000-import choke).
2. AuditStrict.lean only imports lightweight linter/meta modules.
3. Lakefile does not bind monolithic audit gates as prerequisites for standard math libraries.
4. Fast import extraction and dependency hygiene across audit entrypoints.
"""

from __future__ import annotations

import re
from pathlib import Path
import pytest

from tools.infra.audit_default_lean_sources import default_sources, imports
from tools.infra.build_changed_lean import _strip_lean_comments


REPO_ROOT = Path(__file__).resolve().parents[1]


class TestAuditPipelineArchitecture:
    def test_audit_strict_does_not_import_all_exhaustive_or_audit_native(self):
        """AuditStrict must never import AuditNative or AllExhaustive."""
        audit_strict_path = REPO_ROOT / "lean" / "AuditStrict.lean"
        assert audit_strict_path.is_file(), "AuditStrict.lean missing"
        imported_modules = imports(audit_strict_path)

        assert "AuditNative" not in imported_modules, (
            "AuditStrict.lean must NOT import AuditNative! "
            "This causes a transitive import of InfoGeometry.AllExhaustive."
        )
        assert "InfoGeometry.AllExhaustive" not in imported_modules, (
            "AuditStrict.lean must NOT import InfoGeometry.AllExhaustive!"
        )

    def test_audit_strict_imports_only_lean_and_meta(self):
        """AuditStrict should only import Lean frontend and InfoGeometry.Meta/Lint modules."""
        audit_strict_path = REPO_ROOT / "lean" / "AuditStrict.lean"
        imported_modules = imports(audit_strict_path)
        allowed_prefixes = (
            "Lean",
            "InfoGeometry.Lint",
            "InfoGeometry.Meta",
        )
        for mod in imported_modules:
            assert any(mod == prefix or mod.startswith(f"{prefix}.") for prefix in allowed_prefixes), (
                f"Unexpected heavy import in AuditStrict: {mod}"
            )

    def test_trust_propagates_exact_forbidden_axioms_in_source(self):
        """Verify lean/InfoGeometry/Meta/Trust.lean implementation propagates exact forbidden axioms."""
        trust_path = REPO_ROOT / "lean" / "InfoGeometry" / "Meta" / "Trust.lean"
        assert trust_path.is_file(), "Trust.lean missing"
        content = trust_path.read_text(encoding="utf-8")

        # Must have the exact tuple seed and exact mapping propagation
        assert "forbiddenSeeds : Array (Name × Name) := #[]" in content or "forbiddenSeeds : Array" in content, (
            "Trust.lean must declare forbiddenSeeds with exact declaration-axiom pairs"
        )
        assert "forbiddenMap : Std.HashMap Name (Array Name)" in content, (
            "Trust.lean must maintain a map of exact forbidden axioms per declaration"
        )
        assert "defaultForbiddenAxioms else []" not in content, (
            "Trust.lean must not blindly fall back to the entire defaultForbiddenAxioms list"
        )

    def test_lakefile_does_not_couple_math_to_audit_native(self):
        """Ensure core math libraries in lakefile do not list AuditNative or AuditStrict in their roots/globs."""
        lakefile_path = REPO_ROOT / "lakefile.lean"
        assert lakefile_path.is_file()
        content = lakefile_path.read_text(encoding="utf-8")

        # InfoGeometryCanonical should not import or glob audit scripts
        match = re.search(r"lean_lib InfoGeometryCanonical where\n(.*?)(?=^\S|\Z)", content, re.M | re.S)
        assert match, "InfoGeometryCanonical not found in lakefile"
        canonical_body = match.group(1)
        assert "AuditNative" not in canonical_body
        assert "AuditStrict" not in canonical_body

    def test_architecture_attr_module_is_zero_dag_dependency(self):
        """Architecture.lean must stay attribute-only so DAG/audit edits never rebuild 1,800+ math modules."""
        for lane in ("lean", "src"):
            arch_path = REPO_ROOT / lane / "InfoGeometry" / "Meta" / "Architecture.lean"
            assert arch_path.is_file(), f"{arch_path} missing"
            assert imports(arch_path) == {"Lean"}, (
                f"{arch_path} must import only Lean so DAG/audit changes never invalidate math .oleans"
            )

    def test_audit_native_is_lightweight_command_provider(self):
        """AuditNative must not import canonical umbrellas or execute #audit_architecture globally."""
        for lane in ("lean", "src"):
            audit_native_path = REPO_ROOT / lane / "AuditNative.lean"
            assert audit_native_path.is_file(), f"{audit_native_path} missing"
            imported = imports(audit_native_path)
            assert "InfoGeometry.Canonical.All" not in imported
            assert "InfoGeometry.AllExhaustive" not in imported
            stripped = _strip_lean_comments(audit_native_path.read_text(encoding="utf-8"))
            assert not re.search(r"^\s*#audit_architecture\b", stripped, re.M), (
                f"{audit_native_path} must not invoke top-level #audit_architecture"
            )

    def test_audit_entrypoints_are_not_default_targets(self):
        """AuditNative and AuditNativeRun must remain opt-in, not @[default_target] builds."""
        sources = default_sources(REPO_ROOT)
        assert "AuditNative" not in sources
        assert "AuditNativeRun" not in sources

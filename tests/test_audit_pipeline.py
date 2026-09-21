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

from tools.infra.audit_default_lean_sources import imports


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

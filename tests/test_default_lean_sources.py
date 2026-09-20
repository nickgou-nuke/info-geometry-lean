from pathlib import Path
import re

from tools.infra.audit_default_lean_sources import closure, default_sources, imports


def test_imports_ignore_nested_comments_and_normalize_quoted_names(tmp_path):
    source = tmp_path / "Example.lean"
    source.write_text(
        "/- import FalseOwner /- nested -/ -/\n"
        "module\npublic import «VirasoroProject».WittAlgebra\n"
        "import Actual.Owner -- import Another.FalseOwner\n"
        "namespace Example\n", encoding="utf-8")
    assert imports(source) == {"VirasoroProject.WittAlgebra", "Actual.Owner"}


def test_imports_stop_after_header(tmp_path):
    source = tmp_path / "Example.lean"
    source.write_text('import Actual.Owner\ndef text := "import Not.An.Import"\n',
                      encoding="utf-8")
    assert imports(source) == {"Actual.Owner"}


def test_closure_handles_cycles():
    graph = {"All": {"Owner"}, "Owner": {"Helper"}, "Helper": {"Owner"}}
    assert closure({"All"}, graph) == {"All", "Owner", "Helper"}


def test_default_sources_cover_recursive_libraries_and_tests(tmp_path):
    (tmp_path / "lakefile.lean").write_text(
        "@[default_target]\nlean_lib Owner where\n"
        "  globs := #[.andSubmodules `Owner]\n\n"
        "lean_lib Optional where\n  globs := #[.andSubmodules `Optional]\n\n"
        "@[default_target, test_driver]\nlean_lib Tests where\n"
        '  srcDir := "../tests"\n  globs := #[.submodules .anonymous]\n',
        encoding="utf-8")
    for relative in ("lean/Owner.lean", "lean/Owner/Nested.lean", "lean/Optional.lean",
                     "tests/Regression.lean", "tests/nested/Audit.lean"):
        source = tmp_path / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("", encoding="utf-8")
    selected = default_sources(tmp_path)
    assert set(selected) == {"Owner", "Owner.Nested", "Regression", "nested.Audit"}
    assert selected["Regression"] == tmp_path / "tests/Regression.lean"


def test_default_sources_preserve_missing_explicit_roots(tmp_path):
    (tmp_path / "lakefile.lean").write_text(
        "@[default_target]\nlean_lib Standalone where\n"
        "  roots := #[]\n  globs := #[`Missing]\n", encoding="utf-8")
    assert default_sources(tmp_path) == {"Missing": tmp_path / "lean/Missing.lean"}


def test_repository_test_library_owns_only_existing_tests():
    root = Path(__file__).resolve().parents[1]
    config = (root / "lakefile.lean").read_text(encoding="utf-8")
    body = re.search(r"lean_lib InfoGeometryTestSuite where\n(.*?)(?=^\S)",
                     config, re.M | re.S).group(1)
    assert "roots := #[]" in body
    assert ".anonymous" not in body
    declared = set(re.findall(r"`([\w.]+)", body))
    existing = {".".join(path.relative_to(root / "tests").with_suffix("").parts)
                for path in (root / "tests").rglob("*.lean")}
    assert declared == existing
    assert declared.isdisjoint({"Init", "Lean", "Std", "Mathlib", "InfoGeometry"})

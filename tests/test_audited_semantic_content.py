"""Candidate regression suite; parent runs sequentially after source review."""
import importlib.util
import sys
from pathlib import Path
from types import SimpleNamespace
import pytest

BASE = Path(__file__).resolve().parents[1]

def load(relative, name):
    spec = importlib.util.spec_from_file_location(name, BASE / relative)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

construct = load("tools/quality/audit_constructivity.py", "candidate_constructivity")
content = load("tools/quality/semantic_content_audit.py", "candidate_content")
content.audit_constructivity = construct

@pytest.fixture
def corpus(tmp_path, monkeypatch):
    paths = ["lean/InfoGeometry/Owner.lean", "proofs/Other.lean", "lib/Library.lean", "tests/Fixture.lean"]
    for name in paths:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("theorem good : True := by trivial\n")
    monkeypatch.setattr(construct, "ROOT", tmp_path)
    monkeypatch.setattr(content, "ROOT", tmp_path)
    monkeypatch.setattr(construct, "rel", lambda p: Path(p).relative_to(tmp_path).as_posix())
    monkeypatch.setattr(construct.subprocess, "run", lambda *a, **kw: SimpleNamespace(stdout="\0".join(paths) + "\0"))
    monkeypatch.setattr(content, "read_manifest", lambda: ({}, True, None))
    return tmp_path, paths


def test_scope_all_selects_four_roots(corpus):
    root, names = corpus
    assert {content.rel(p) for p in content.all_lean_files(scope="all")} == set(names)
    assert {content.rel(p) for p in content.all_lean_files(scope="stable")} == set(names)
    unstable = root / "lean/InfoGeometry/Unstable/Quarantined.lean"
    unstable.parent.mkdir(parents=True)
    unstable.write_text("theorem sample : True := by trivial\n")
    names.append("lean/InfoGeometry/Unstable/Quarantined.lean")
    assert "lean/InfoGeometry/Unstable/Quarantined.lean" not in {
        content.rel(p) for p in content.all_lean_files(scope="stable")}
    assert {content.rel(p) for p in content.all_lean_files(scope="quarantine")} == {
        "lean/InfoGeometry/Unstable/Quarantined.lean"}


def test_missing_selected_file_is_failed_coverage(corpus):
    root, names = corpus
    (root / names[-1]).unlink()
    report = content.build_report(scope="all", include_review=False, excerpt_radius=1, include_manifest_consistency=False)
    assert report["coverage"]["files_selected"] == 4
    assert report["coverage"]["files_read"] == 3
    assert not report["coverage"]["coverage_complete"]
    assert any(f["file"] == names[-1] for f in report["coverage"]["read_failures"])
    with pytest.raises(FileNotFoundError):
        construct.scan_file(root / names[-1])


def test_multiimports_and_namespace_scopes(corpus):
    root, names = corpus
    path = root / names[0]
    path.write_text("import InfoGeometry.A InfoGeometry.B\nnamespace Outer\nsection S\nnamespace Inner\n@[simp] theorem a : True := by trivial\nend Inner\nend S\ntheorem b : True := by trivial\nend Outer\ntheorem c : True := by trivial\n")
    imports = content.importers_by_module([path])
    assert set(imports) == {"InfoGeometry.A", "InfoGeometry.B"}
    headers = content.declaration_headers(path, "InfoGeometry.Owner")
    assert [h["name"] for h in headers] == ["Outer.Inner.a", "Outer.b", "c"]
    assert all(h["name_resolution"] == "lexical_approximation_not_elaborated" for h in headers)


def test_nested_comments_preserve_coordinates(corpus):
    root, names = corpus
    path = root / names[0]
    raw = '/- ignored /- sorry -/ ignored -/\ntheorem bad : True := by sorry\n'
    path.write_text(raw)
    masked = construct.strip_comments(raw, strip_strings=True)
    assert len(masked) == len(raw)
    findings = construct.scan_file(path)
    assert [(f.category, f.line) for f in findings] == [("proof-hole", 2)]


def test_invalid_utf8_and_empty_scope_fail(corpus):
    root, names = corpus
    (root / names[0]).write_bytes(b"\xff")
    report = content.build_report(scope="all", include_review=False, excerpt_radius=1, include_manifest_consistency=False)
    assert not report["coverage"]["coverage_complete"]
    assert report["coverage"]["files_read"] == 3
    report = content.build_report(scope="all", include_review=False, excerpt_radius=1, include_manifest_consistency=False, file_prefixes=["no-such-prefix/"])
    assert report["coverage"]["files_selected"] == 0
    assert not report["coverage"]["coverage_complete"]

"""Regression tests for audited source-tool repairs; not Lean verification."""
import importlib.util
import sys
from pathlib import Path
import pytest

BASE = Path(__file__).resolve().parents[1]

def load(relative, name):
    spec = importlib.util.spec_from_file_location(name, BASE / relative)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod

extract = load("tools/leantrail/ast_extract.py", "candidate_extract")
clique = load("tools/leantrail/ast_aql_clique_analysis.py", "candidate_clique")
gate = load("tools/quality/semantic_vacuity_gate.py", "candidate_gate")

@pytest.mark.parametrize("surface", ["lean", "proofs"])
def test_long_body_hole_and_paths(tmp_path, surface):
    folder = tmp_path / surface
    folder.mkdir()
    source = folder / "Owner.lean"
    source.write_text("namespace Owner\n@[simp] theorem α : True := by\n" +
                      "  skip\n" * 30 + "  sorry\n" +
                      "theorem good : True := by trivial\n")
    extract.REPO_ROOT = tmp_path
    graph = extract.extract_graph(folder)
    assert graph["meta"]["files_read"] == graph["meta"]["files_selected"] == 1
    assert graph["nodes"][0]["file"] == f"{surface}/Owner.lean"
    result = clique.inspect_node_sources(graph["nodes"], tmp_path)
    assert result["contaminated"] == {graph["nodes"][0]["id"]}
    assert not result["unknown"]


def test_comments_strings_do_not_hide_real_hole(tmp_path):
    source = 'theorem foo\' : True := by\n  let s := "sorry"; sorry -- admit\n/- sorry /- admit -/ -/\n'
    findings = gate.audit_text("Fixture.lean", source, {})
    assert len([f for f in findings if f.category == "placeholder_token"]) == 1
    masked = gate.strip_comments(source, mask_literals=True)
    assert len(masked) == len(source)
    assert masked.count("\n") == source.count("\n")


def test_semantic_gate_ignores_qualified_admit_but_finds_hole():
    source = """def traceName := ``Lean.Parser.Term.«sorry»
def qualified := DAG.Morphism.admit
theorem missing : True := by
  sorry
"""
    findings = gate.audit_text("Fixture.lean", source, {})
    holes = [f for f in findings if f.category == "placeholder_token"]
    assert len(holes) == 1
    assert holes[0].line == 4


def test_semantic_gate_detects_private_axiom():
    findings = gate.audit_text(
        "Fixture.lean", "private axiom hidden : False\n", {}
    )
    assert len([f for f in findings if f.category == "placeholder_token"]) == 1


def test_theorem_window_skips_binder_default_assignment():
    lines = ["theorem missing (n : Nat := 1) : True := by", "  sorry"]
    body = gate.theorem_window(lines, 0)
    assert body.startswith("by")
    assert ":= 1" not in body
    assert "sorry" in body


def test_proof_only_certificate_is_review_warning_but_empty_model_is_error():
    from tools.quality.semantic_vacuity_gate import DEFAULT_PATTERNS, load_patterns

    categories = load_patterns(DEFAULT_PATTERNS)["categories"]
    findings = gate.audit_text(
        "Fixture.lean",
        """structure ProofCertificate : Prop where
  law : ∀ n : Nat, n = n

structure EmptyModelWitness where
""",
        categories,
    )
    carrier_findings = [f for f in findings if f.category == "pure_proof_carrier"]
    assert [(f.subject, f.severity) for f in carrier_findings] == [
        ("ProofCertificate", "warning"),
        ("EmptyModelWitness", "error"),
    ]


def test_missing_sources_are_unknown(tmp_path):
    node = {"id": "missing", "file": "lean/Missing.lean", "line": 1}
    result = clique.inspect_node_sources([node], tmp_path)
    assert result["unknown"] == {"missing"}
    assert result["files_read"] == 0
    assert result["read_failures"]
    with pytest.raises(FileNotFoundError):
        gate.audit_file(tmp_path / "missing.lean", {})
    with pytest.raises(FileNotFoundError):
        extract.extract_graph(tmp_path / "missing")


def test_invalid_utf8_is_failed_read(tmp_path):
    source = tmp_path / "Broken.lean"
    source.write_bytes(b"\xff")
    graph = extract.extract_graph(tmp_path)
    assert graph["meta"]["files_selected"] == 1
    assert graph["meta"]["files_read"] == 0
    assert not graph["meta"]["coverage_complete"]


def test_stale_span_is_unknown(tmp_path):
    source = tmp_path / "Owner.lean"
    source.write_text("theorem good : True := by trivial\n")
    graph = extract.extract_graph(tmp_path)
    source.write_text("theorem bad : True := by sorry\n")
    result = clique.inspect_node_sources(graph["nodes"], tmp_path)
    assert result["unknown"] == {graph["nodes"][0]["id"]}


def test_full_theorem_window_stops_next_declaration():
    lines = ["theorem a : True := by"] + ["  skip"] * 40 + ["  sorry", "@[simp] theorem b : True := by trivial"]
    body = gate.theorem_window(lines, 0)
    assert "sorry" in body
    assert "theorem b" not in body

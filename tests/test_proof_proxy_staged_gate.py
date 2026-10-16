import subprocess

from tools.quality.proof_proxy_staged_gate import (
    REQUIRED_LEAN_COPYRIGHT_HEADER,
    aggregate_prop_constructors,
    check_text,
    main,
)

EXPECTED_LEAN_COPYRIGHT_HEADER = (
    "/-\n"
    "Copyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: InfoGeometry Engine Contributors\n"
    "-/\n"
)


def test_required_copyright_header_matches_repository_standard_exactly():
    assert REQUIRED_LEAN_COPYRIGHT_HEADER == EXPECTED_LEAN_COPYRIGHT_HEADER


def test_staged_lean_source_requires_exact_copyright_and_license_header():
    source = EXPECTED_LEAN_COPYRIGHT_HEADER + "theorem header_check : True := trivial\n"
    assert check_text("Owner.lean", source) == []


def test_staged_lean_source_rejects_missing_or_malformed_copyright_header():
    source = "-- missing required block header\ntheorem header_check : True := trivial\n"
    failures = check_text("Owner.lean", source)
    assert len(failures) == 1
    assert "missing or malformed required InfoGeometry copyright and license header" in failures[0]


def test_staged_lean_source_rejects_a_header_with_wrong_license_text():
    source = EXPECTED_LEAN_COPYRIGHT_HEADER.replace("Apache 2.0", "MIT")
    failures = check_text("Owner.lean", source)
    assert len(failures) == 1
    assert "missing or malformed required InfoGeometry copyright and license header" in failures[0]


def test_precommit_gate_checks_lean_file_replaced_by_symlink(tmp_path, monkeypatch, capsys):
    def git(*args):
        return subprocess.run(
            ["git", *args], cwd=tmp_path, check=True, capture_output=True, text=True
        ).stdout

    git("init", "-q")
    git("config", "user.email", "hook-test@example.invalid")
    git("config", "user.name", "Hook Test")
    owner = tmp_path / "Owner.lean"
    owner.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "theorem ok : True := trivial\n")
    git("add", "Owner.lean")
    git("commit", "-qm", "baseline")

    owner.unlink()
    owner.symlink_to("headerless-target")
    git("add", "-A")
    assert git("diff", "--cached", "--name-status") == "T\tOwner.lean\n"
    monkeypatch.chdir(tmp_path)

    assert main() == 1
    assert "missing or malformed required InfoGeometry copyright and license header" in capsys.readouterr().err


def test_aggregate_prop_proof_wrapper_is_detected_without_name_keywords():
    source = """
structure Output : Prop where
  first_claim : FirstClaim
  second_claim : SecondClaim

theorem assemble_output : Output where
  first_claim := first_claim_proved
  second_claim := second_claim_proved
"""
    found = aggregate_prop_constructors(source)
    assert len(found) == 1
    assert found[0][0] == "Output"


def test_mathematical_predicate_structure_is_not_a_proof_bundle():
    source = """
structure IsDrazinOperator (A D : R) (k : Nat) : Prop where
  drazin_one : D * A * D = D
  comm : A * D = D * A
  index_law : A ^ (k + 1) * D = A ^ k
"""
    assert aggregate_prop_constructors(source) == []


def test_prop_structure_with_non_keyword_fields_is_caught_by_assembly():
    source = """
structure CarrierInvariant : Prop where
  alpha : Alpha
  beta : Beta

theorem build_invariant : CarrierInvariant where
  alpha := alpha_owner
  beta := beta_owner
"""
    assert aggregate_prop_constructors(source) == [("CarrierInvariant", "theorem build_invariant : CarrierInvariant where")]

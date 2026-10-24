import os
import subprocess

from tools.quality.proof_proxy_staged_gate import (
    ActiveIndexCache,
    REQUIRED_LEAN_COPYRIGHT_HEADER,
    aggregate_prop_constructors,
    check_text,
    imported_source_index_mismatches,
    materialize_indexed_imports,
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


def _init_hook_repo(tmp_path, monkeypatch):
    def git(*args):
        return subprocess.run(
            ["git", *args], cwd=tmp_path, check=True, capture_output=True, text=True
        ).stdout

    git("init", "-q")
    git("config", "user.email", "hook-test@example.invalid")
    git("config", "user.name", "Hook Test")
    baseline = tmp_path / "baseline.txt"
    baseline.write_text("baseline\n")
    git("add", "baseline.txt")
    git("commit", "-qm", "baseline")
    monkeypatch.chdir(tmp_path)
    return git


def test_active_index_cache_detects_index_mutation(tmp_path, monkeypatch):
    git = _init_hook_repo(tmp_path, monkeypatch)
    cache = ActiveIndexCache(tmp_path)
    assert cache.still_current()

    tracked = tmp_path / "baseline.txt"
    tracked.write_text("updated baseline\n")
    git("add", "baseline.txt")

    assert not cache.still_current()


def test_active_index_cache_ignores_metadata_only_index_refresh(tmp_path, monkeypatch):
    git = _init_hook_repo(tmp_path, monkeypatch)
    cache = ActiveIndexCache(tmp_path)
    index_path = tmp_path / git("rev-parse", "--git-path", "index").strip()
    before = index_path.stat()

    # Git's stat cache can be refreshed without changing staged entries.
    os.utime(index_path, ns=(before.st_atime_ns, before.st_mtime_ns + 1_000_000))

    assert cache.still_current()


def test_active_index_cache_rejects_unavailable_index(tmp_path, monkeypatch):
    _init_hook_repo(tmp_path, monkeypatch)
    monkeypatch.setenv("GIT_INDEX_FILE", str(tmp_path / "missing-index"))
    cache = ActiveIndexCache(tmp_path)
    assert not cache.still_current()


def test_active_index_import_cache_survives_both_import_traversals(
    tmp_path, monkeypatch
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    imported = tmp_path / "lean" / "Fixture" / "Imported.lean"
    imported.parent.mkdir(parents=True)
    imported.write_text("theorem imported_owner : True := trivial\n")
    git("add", "lean/Fixture/Imported.lean")
    git("commit", "-qm", "add imported owner")

    source = "import Fixture.Imported\ntheorem local_owner : True := trivial\n"
    cache = ActiveIndexCache(tmp_path)
    assert imported_source_index_mismatches(source, tmp_path, cache) == []
    snapshot = tmp_path / "snapshot"
    assert materialize_indexed_imports(source, tmp_path, snapshot, cache) == []
    assert (snapshot / "lean" / "Fixture" / "Imported.lean").read_text() == (
        "theorem imported_owner : True := trivial\n"
    )


def test_precommit_gate_rejects_renamed_vacuous_prop_from_staged_blob(
    tmp_path, monkeypatch, capsys
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    owner = tmp_path / "Owner.lean"
    owner.write_text(
        EXPECTED_LEAN_COPYRIGHT_HEADER
        + "def UnrelatedInvariant : Prop := True\n"
    )
    git("add", "Owner.lean")

    assert main() == 1
    stderr = capsys.readouterr().err
    assert "OpenGauss T4" in stderr
    assert "UnrelatedInvariant" in stderr


def test_precommit_gate_rejects_renamed_scalar_surrogate_from_staged_blob(
    tmp_path, monkeypatch, capsys
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    owner = tmp_path / "Owner.lean"
    owner.write_text(
        EXPECTED_LEAN_COPYRIGHT_HEADER
        + "structure CarrierData where\n"
        + "  tr_left : Float\n"
        + "  detRight : Float\n"
    )
    git("add", "Owner.lean")

    assert main() == 1
    stderr = capsys.readouterr().err
    assert "OpenGauss T16" in stderr
    assert "CarrierData" in stderr


def test_precommit_gate_rejects_imported_source_that_differs_from_active_index(
    tmp_path, monkeypatch, capsys
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    imported = tmp_path / "lean" / "Fixture" / "Imported.lean"
    imported.parent.mkdir(parents=True)
    imported.write_text("theorem imported_owner : True := trivial\n")
    git("add", "lean/Fixture/Imported.lean")
    git("commit", "-qm", "add imported owner")

    imported.write_text("axiom unstaged_change : True\n")
    owner = tmp_path / "Owner.lean"
    owner.write_text(
        EXPECTED_LEAN_COPYRIGHT_HEADER
        + "import Fixture.Imported\n"
        + "theorem local_owner : True := trivial\n"
    )
    git("add", "Owner.lean")

    assert main() == 1
    stderr = capsys.readouterr().err
    assert "imported Lean source is not a consistent active-index snapshot" in stderr
    assert "lean/Fixture/Imported.lean" in stderr


def test_precommit_gate_rejects_imported_source_missing_from_worktree_but_in_index(
    tmp_path, monkeypatch, capsys
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    imported = tmp_path / "lean" / "Fixture" / "Imported.lean"
    imported.parent.mkdir(parents=True)
    imported.write_text("theorem imported_owner : True := trivial\n")
    git("add", "lean/Fixture/Imported.lean")
    git("commit", "-qm", "add imported owner")
    imported.unlink()

    owner = tmp_path / "Owner.lean"
    owner.write_text(
        EXPECTED_LEAN_COPYRIGHT_HEADER
        + "import Fixture.Imported\n"
        + "theorem local_owner : True := trivial\n"
    )
    git("add", "Owner.lean")

    assert main() == 1
    stderr = capsys.readouterr().err
    assert "imported Lean source is not a consistent active-index snapshot" in stderr
    assert "present in active index but missing from worktree" in stderr


def test_import_consistency_checks_missing_precedence_root_with_fallback_copy(
    tmp_path, monkeypatch
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    preferred = tmp_path / "lean" / "Fixture" / "Imported.lean"
    fallback = tmp_path / "proofs" / "Fixture" / "Imported.lean"
    preferred.parent.mkdir(parents=True)
    fallback.parent.mkdir(parents=True)
    preferred.write_text("theorem preferred_owner : True := trivial\n")
    fallback.write_text("theorem fallback_owner : True := trivial\n")
    git("add", "lean/Fixture/Imported.lean", "proofs/Fixture/Imported.lean")
    git("commit", "-qm", "add duplicate-root imports")
    preferred.unlink()

    source = "import Fixture.Imported\ntheorem local_owner : True := trivial\n"
    mismatches = imported_source_index_mismatches(source, tmp_path)
    assert any(
        "lean/Fixture/Imported.lean" in item and "missing from worktree" in item
        for item in mismatches
    ), mismatches


def test_import_consistency_guard_uses_git_commit_only_active_index(
    tmp_path, monkeypatch
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    imported = tmp_path / "lean" / "Fixture" / "Imported.lean"
    imported.parent.mkdir(parents=True)
    imported.write_text("theorem imported_owner : True := trivial\n")
    git("add", "lean/Fixture/Imported.lean")
    git("commit", "-qm", "add imported owner")

    imported.write_text("theorem imported_owner : True := by exact True.intro\n")
    git("add", "lean/Fixture/Imported.lean")
    owner_source = (
        EXPECTED_LEAN_COPYRIGHT_HEADER
        + "import Fixture.Imported\n"
        + "theorem local_owner : True := trivial\n"
    )
    (tmp_path / "Owner.lean").write_text(owner_source)

    # `git commit --only Owner.lean` supplies an index based on HEAD plus the
    # selected owner, excluding the staged imported-source update. Exercise
    # that same index routing without invoking a commit hook recursively.
    temporary_index = tmp_path / "only.index"
    env = dict(os.environ)
    env["GIT_INDEX_FILE"] = str(temporary_index)
    subprocess.run(
        ["git", "read-tree", "HEAD"], cwd=tmp_path, env=env, check=True
    )
    subprocess.run(
        ["git", "add", "Owner.lean"], cwd=tmp_path, env=env, check=True
    )
    monkeypatch.setenv("GIT_INDEX_FILE", str(temporary_index))

    mismatches = imported_source_index_mismatches(owner_source, tmp_path)
    assert any("worktree differs from active index" in item for item in mismatches)


def test_import_snapshot_materializes_active_index_bytes_not_worktree_bytes(
    tmp_path, monkeypatch
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    imported = tmp_path / "lean" / "Fixture" / "Imported.lean"
    imported.parent.mkdir(parents=True)
    indexed_source = "theorem imported_owner : True := trivial\n"
    imported.write_text(indexed_source)
    git("add", "lean/Fixture/Imported.lean")
    git("commit", "-qm", "add imported owner")
    imported.write_text("axiom worktree_only : True\n")

    snapshot = tmp_path / "snapshot"
    errors = materialize_indexed_imports(
        "import Fixture.Imported\n", tmp_path, snapshot
    )

    assert errors == []
    assert (snapshot / "lean/Fixture/Imported.lean").read_text() == indexed_source


def test_import_consistency_guard_rejects_repo_local_symlink_import(
    tmp_path, monkeypatch
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    external = tmp_path / "outside.lean"
    external.write_text("theorem imported_owner : True := trivial\n")
    imported = tmp_path / "lean" / "Fixture" / "Imported.lean"
    imported.parent.mkdir(parents=True)
    imported.symlink_to(external)
    git("add", "lean/Fixture/Imported.lean")
    git("commit", "-qm", "add symlink import")

    mismatches = imported_source_index_mismatches(
        "import Fixture.Imported\n", tmp_path
    )

    assert any("may not be symlinks" in item for item in mismatches), mismatches


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


def test_precommit_gate_detects_multiline_block_comment_debt_burial_and_quote_bypass(
    tmp_path, monkeypatch, capsys
):
    git = _init_hook_repo(tmp_path, monkeypatch)
    owner = tmp_path / "Owner.lean"
    owner.write_text(
        REQUIRED_LEAN_COPYRIGHT_HEADER
        + "theorem old_owner : True := trivial\n"
        + "theorem kept_owner : True := trivial\n"
    )
    git("add", "Owner.lean")
    git("commit", "-qm", "baseline")

    owner.write_text(
        REQUIRED_LEAN_COPYRIGHT_HEADER
        + "/-!\n"
        + "The previous contradictory rank-five pairing interface is not needed here.\n"
        + "-/\n"
        + "theorem kept_owner : True := by\n"
        + '  sorry -- "quoted comment cannot bypass sorry scan"\n'
    )
    git("add", "Owner.lean")
    monkeypatch.chdir(tmp_path)

    assert main(["Owner.lean"]) == 1
    err = capsys.readouterr().err
    assert "staged deletion of Lean declarations with natural-language debt comments" in err
    assert "staged forbidden placeholder" in err

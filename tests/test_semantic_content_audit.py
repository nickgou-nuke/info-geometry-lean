from pathlib import Path

from tools.quality.semantic_content_audit import (
    STATUS_PRECEDENCE,
    build_report,
    declaration_headers,
    enclosing_decl,
    forbidden_importers_for_status,
    in_scope,
    importer_class,
    importers_by_module,
    semantic_status,
)


def test_proof_hole_blocks_before_other_categories() -> None:
    status, action = semantic_status({"proof-hole", "trivial-theorem"})

    assert status == "proof_hole_blocker"
    assert "quarantine" in action


def test_axiom_is_assumption_bearing_blocker() -> None:
    status, action = semantic_status({"axiom"})

    assert status == "explicit_axiom_blocker"
    assert "hypothesis context" in action


def test_trivial_true_surface_is_vacuous_review_not_canonical() -> None:
    status, action = semantic_status({"prop-constant", "trivial-theorem"})

    assert status == "vacuous_or_surrogate_surface"
    assert "True/trivial" in action


def test_clean_surface_is_only_clean_by_this_audit() -> None:
    status, action = semantic_status(set())

    assert status == "content_clean_by_this_audit"
    assert "this audit" in action


def test_quarantine_manifest_has_own_status() -> None:
    status, action = semantic_status({"quarantine-manifest"})

    assert status == "quarantine_manifest_inconsistency"
    assert "manifest" in action
    assert status in STATUS_PRECEDENCE


def test_commented_import_is_not_counted_as_importer(tmp_path: Path) -> None:
    src = tmp_path / "lean" / "InfoGeometry"
    src.mkdir(parents=True)
    importer = src / "Importer.lean"
    importer.write_text("-- import InfoGeometry.Hidden\nimport InfoGeometry.Real\n", encoding="utf-8")

    imports = importers_by_module([importer])

    assert "InfoGeometry.Hidden" not in imports
    assert len(imports["InfoGeometry.Real"]) == 1
    assert imports["InfoGeometry.Real"][0].endswith("lean.InfoGeometry.Importer")


def test_importer_classes_separate_unstable_umbrella_and_canonical() -> None:
    assert importer_class("InfoGeometry.Unstable.Quarantine") == "allowed_unstable"
    assert importer_class("InfoGeometry.All") == "umbrella"
    assert importer_class("InfoGeometry.Canonical.All") == "umbrella"
    assert importer_class("Other.All") == "other"
    assert importer_class("InfoGeometry.Canonical.Core") == "canonical"
    assert importer_class("InfoGeometry.OperatorAlgebra.Core") == "other"


def test_forbidden_importers_apply_to_nonpromotable_statuses() -> None:
    forbidden = forbidden_importers_for_status(
        "vacuous_or_surrogate_surface",
        [
            "InfoGeometry.Unstable.Quarantine",
            "InfoGeometry.Canonical.All",
            "InfoGeometry.Canonical.Core",
            "InfoGeometry.OperatorAlgebra.Core",
        ],
    )

    assert "InfoGeometry.Unstable.Quarantine" not in forbidden
    assert "InfoGeometry.Canonical.All" in forbidden
    assert "InfoGeometry.Canonical.Core" in forbidden
    assert "InfoGeometry.OperatorAlgebra.Core" in forbidden


def test_manifested_clean_quarantine_still_has_forbidden_importers() -> None:
    forbidden = forbidden_importers_for_status(
        "manifested_quarantine_no_current_findings",
        ["InfoGeometry.Canonical.All", "InfoGeometry.Unstable.Quarantine"],
    )

    assert "InfoGeometry.Canonical.All" in forbidden
    assert "InfoGeometry.Unstable.Quarantine" not in forbidden


def test_manifest_only_rows_preserve_forbidden_importer_metadata(monkeypatch, tmp_path) -> None:
    from tools.quality import semantic_content_audit as audit

    monkeypatch.setattr(audit, "ROOT", tmp_path)
    manifest_path = tmp_path / "lean" / "InfoGeometry" / "Quarantine" / "Clean.lean"
    manifest_path.parent.mkdir(parents=True)
    manifest_path.write_text("namespace InfoGeometry.Quarantine\ndef clean : Nat := 1\n")
    monkeypatch.setattr(audit, "read_manifest", lambda: ({"InfoGeometry.Quarantine.Clean": "review"}, True, None))
    monkeypatch.setattr(audit, "module_to_path", lambda module: manifest_path)
    monkeypatch.setattr(audit, "all_infogeometry_files", lambda **kwargs: [manifest_path] if kwargs.get("scope") == "all" else [])
    monkeypatch.setattr(
        audit,
        "importers_by_module",
        lambda files=None, **kwargs: {"InfoGeometry.Quarantine.Clean": ["InfoGeometry.Canonical.All"]},
    )
    def no_findings(*args, **kwargs):
        kwargs["successful"].append(audit.rel(manifest_path))
        return []
    monkeypatch.setattr(audit, "collect_findings", no_findings)

    report = audit.build_report(include_review=False, excerpt_radius=1)

    assert report["summary"]["manifest_only_module_count"] == 1
    module = report["modules"][0]
    assert module["semantic_status"] == "manifested_quarantine_no_current_findings"
    assert module["forbidden_importer_count"] == 1
    assert module["forbidden_importers"] == ["InfoGeometry.Canonical.All"]


def test_in_scope_applies_file_prefixes_to_manifest_rows() -> None:
    path = Path("lean/InfoGeometry/Projective/TwistorBridge.lean")

    assert not in_scope(
        path,
        file_prefixes=["lean/InfoGeometry/Canonical"],
        manifest_modules={"InfoGeometry.Projective.TwistorBridge"},
    )


def test_gate_empty_selection_is_reported_by_selected_file_count() -> None:
    report = build_report(
        include_review=False,
        excerpt_radius=1,
        file_prefixes=["lean/InfoGeometry/DefinitelyMissingPrefix"],
        include_manifest_consistency=False,
    )

    assert report["summary"]["selected_file_count"] == 0
    assert report["summary"]["modules_reported"] == 0


def test_enclosing_decl_finds_nearest_preceding_declaration(tmp_path: Path) -> None:
    path = tmp_path / "M.lean"
    path.write_text(
        "namespace M\n\n"
        "def a : Nat := 0\n\n"
        "theorem t : True := by\n"
        "  trivial\n",
        encoding="utf-8",
    )

    headers = declaration_headers(path, "M")
    owner = enclosing_decl(headers, 6)

    assert owner is not None
    assert owner["name"] == "M.t"
    assert owner["kind"] == "theorem"


def test_clean_incremental_build_report_skips_full_repo_importer_scan(monkeypatch, tmp_path: Path) -> None:
    from tools.quality import semantic_content_audit as audit

    clean = tmp_path / "lean" / "InfoGeometry" / "Clean.lean"
    clean.parent.mkdir(parents=True)
    clean.write_text("namespace Clean\ndef ok : Nat := 1\n", encoding="utf-8")

    monkeypatch.setattr(audit, "ROOT", tmp_path)
    monkeypatch.setattr(audit, "read_manifest", lambda: ({}, True, None))
    monkeypatch.setattr(audit.audit_constructivity, "maintained_lean_files", lambda **kw: [clean])
    monkeypatch.setattr(
        audit,
        "importers_by_module",
        lambda *a, **kw: (_ for _ in ()).throw(AssertionError("unexpected full importer scan")),
    )

    report = audit.build_report(
        include_review=False,
        excerpt_radius=1,
        file_prefixes=["lean/InfoGeometry/Clean.lean"],
        include_manifest_consistency=False,
    )

    assert report["summary"]["selected_file_count"] == 1
    assert report["summary"]["modules_reported"] == 0


def test_all_lean_files_passes_include_src_only_for_src_prefix(monkeypatch, tmp_path: Path) -> None:
    from tools.quality import semantic_content_audit as audit

    recorded: list[dict[str, object]] = []

    def fake_maintained(**kwargs):
        recorded.append(dict(kwargs))
        return [
            tmp_path / "lean" / "InfoGeometry" / "A.lean",
            tmp_path / "src" / "InfoGeometry" / "B.lean",
        ]

    monkeypatch.setattr(audit, "ROOT", tmp_path)
    monkeypatch.setattr(audit.audit_constructivity, "maintained_lean_files", fake_maintained)

    src_selected = audit.all_lean_files(file_prefixes=["src/InfoGeometry/B.lean"])
    lean_selected = audit.all_lean_files(file_prefixes=["lean/InfoGeometry/A.lean"])

    assert [p.relative_to(tmp_path).as_posix() for p in src_selected] == ["src/InfoGeometry/B.lean"]
    assert [p.relative_to(tmp_path).as_posix() for p in lean_selected] == ["lean/InfoGeometry/A.lean"]
    assert recorded == [{"include_src": True}, {}]


def test_importers_by_module_target_modules_prefilters_unrelated_files(monkeypatch, tmp_path: Path) -> None:
    from tools.quality import semantic_content_audit as audit

    unrelated = tmp_path / "lean" / "InfoGeometry" / "Unrelated.lean"
    user = tmp_path / "lean" / "InfoGeometry" / "User.lean"
    unrelated.parent.mkdir(parents=True)
    unrelated.write_text("import Mathlib\ndef x : Nat := 1\n", encoding="utf-8")
    user.write_text("import InfoGeometry.Target\ndef y : Nat := 2\n", encoding="utf-8")

    monkeypatch.setattr(audit, "ROOT", tmp_path)
    stripped_calls: list[str] = []
    orig_strip = audit.audit_constructivity.strip_comments

    def spy_strip(text: str, **kwargs):
        stripped_calls.append(text)
        return orig_strip(text, **kwargs)

    monkeypatch.setattr(audit.audit_constructivity, "strip_comments", spy_strip)
    imports = audit.importers_by_module([unrelated, user], target_modules={"InfoGeometry.Target"})

    assert imports == {"InfoGeometry.Target": ["InfoGeometry.User"]}
    assert len(stripped_calls) == 1
    assert "InfoGeometry.Target" in stripped_calls[0]


def test_main_scoped_defaults_write_under_artifacts_not_global_reports(monkeypatch, tmp_path: Path) -> None:
    import sys
    from tools.quality import semantic_content_audit as audit

    clean = tmp_path / "lean" / "InfoGeometry" / "Clean.lean"
    clean.parent.mkdir(parents=True)
    clean.write_text("def ok : Nat := 1\n", encoding="utf-8")

    monkeypatch.setattr(audit, "ROOT", tmp_path)
    monkeypatch.setattr(audit, "read_manifest", lambda: ({}, True, None))
    monkeypatch.setattr(audit.audit_constructivity, "maintained_lean_files", lambda **kw: [clean])
    monkeypatch.setattr(sys, "argv", ["semantic_content_audit.py", "--file-prefix", "lean/InfoGeometry/Clean.lean", "--gate"])

    rc = audit.main()

    assert rc == 0
    assert (tmp_path / "artifacts" / "semantic-content-audit-scoped.json").is_file()
    assert (tmp_path / "artifacts" / "semantic-content-audit-scoped.md").is_file()
    assert not (tmp_path / "reports" / "dag" / "semantic-content-audit.json").exists()


def test_in_scope_exact_lean_file_prefix_avoids_sibling_collision(monkeypatch, tmp_path: Path) -> None:
    from tools.quality import semantic_content_audit as audit

    monkeypatch.setattr(audit, "ROOT", tmp_path)
    exact = tmp_path / "lean" / "InfoGeometry" / "Test.lean"
    sibling = tmp_path / "lean" / "InfoGeometry" / "TestExtra.lean"
    assert in_scope(exact, file_prefixes=["lean/InfoGeometry/Test.lean"])
    assert not in_scope(sibling, file_prefixes=["lean/InfoGeometry/Test.lean"])

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


def test_manifest_only_rows_preserve_forbidden_importer_metadata(monkeypatch) -> None:
    from tools.quality import semantic_content_audit as audit

    manifest_path = audit.ROOT / "lean" / "InfoGeometry" / "Quarantine" / "Clean.lean"
    monkeypatch.setattr(audit, "read_manifest", lambda: ({"InfoGeometry.Quarantine.Clean": "review"}, True, None))
    monkeypatch.setattr(audit, "module_to_path", lambda module: manifest_path)
    monkeypatch.setattr(audit, "all_infogeometry_files", lambda **kwargs: [manifest_path] if kwargs.get("scope") == "all" else [])
    monkeypatch.setattr(
        audit,
        "importers_by_module",
        lambda files=None: {"InfoGeometry.Quarantine.Clean": ["InfoGeometry.Canonical.All"]},
    )
    monkeypatch.setattr(audit, "collect_findings", lambda *args, **kwargs: [])

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

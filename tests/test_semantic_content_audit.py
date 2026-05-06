from pathlib import Path

from tools.quality.semantic_content_audit import (
    forbidden_importers_for_status,
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

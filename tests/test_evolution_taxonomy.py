from __future__ import annotations

from tools.infra.evolution_taxonomy import CATEGORY_IDS, classify, iter_labels


def test_classify_emits_nonhierarchical_facets_with_evidence() -> None:
    labels = classify(
        "Fix and refactor the Lean tests",
        "",
        ["tests/test_graph.py", "README.md"],
    )

    by_category = {label["category"]: label for label in labels}
    assert {"Bug Fix", "Refactor/Restructure", "Test Evolution",
            "Documentation/Developer UX"} <= set(by_category)
    assert all(label["status"] == "weak_rule" for label in labels)
    assert all(label["categoryId"] == CATEGORY_IDS[label["category"]]
               for label in labels)
    assert all(0 <= label["ruleWeightPercent"] <= 100 for label in labels)
    assert "confidence" not in labels[0]
    assert all(label["evidence"] and label["evidenceKinds"] for label in labels)


def test_unmatched_commit_is_labeled_as_weak_default_not_species() -> None:
    labels = classify("miscellaneous work", "", [])

    assert labels == [{
        "category": "Feature Introduction",
        "categoryId": "featureIntroduction",
        "ruleWeightPercent": 40,
        "evidence": ["default:no-rule-match"],
        "evidenceKinds": ["defaultNoRuleMatch"],
        "status": "weak_rule",
    }]
    assert "species" not in labels[0]


def test_streamed_labels_have_versioned_schema_and_keep_commit_identity() -> None:
    records = [{
        "type": "commit",
        "sha": "abc123",
        "subject": "fix parser",
        "body": "",
        "paths": ["src/parser.py"],
    }]

    [row] = list(iter_labels(records))
    assert row["schema"] == "info_geometry.commit_change_labels.v1"
    assert row["method"] == "weak-rule-v3"
    assert row["sha"] == "abc123"
    assert row["labels"][0]["category"] == "Bug Fix"

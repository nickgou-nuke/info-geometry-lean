from __future__ import annotations

import copy
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

from tools.infra.evolution_taxonomy import (
    CATEGORY_IDS,
    EVIDENCE_KINDS,
    GEM_CLADE_IDS,
    GEM_EPOCH_IDS,
    METHOD_VERSION,
    SCHEMA_VERSION,
    classify,
    iter_labels,
    validate_jsonl_file,
    validate_label_record,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_CONTRACT_FILE = REPO_ROOT / "lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean"
LEAN_GEM_POSET_FILE = REPO_ROOT / "lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean"


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
    # Regression check for lines 89-90: when both a subject/body rule and a path
    # hint match the same category ("Test Evolution"), evidenceKinds must include both.
    assert by_category["Test Evolution"]["evidence"] == [
        "subject-body-rule:Test Evolution",
        "path-hint:Test Evolution",
    ]
    assert by_category["Test Evolution"]["evidenceKinds"] == [
        "pathHint",
        "subjectBodyRule",
    ]
    assert by_category["Documentation/Developer UX"]["evidenceKinds"] == ["pathHint"]


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
    assert row["schema"] == SCHEMA_VERSION == "info_geometry.commit_change_labels.v1"
    assert row["method"] == METHOD_VERSION == "weak-rule-v3"
    assert row["sha"] == "abc123"
    assert row["labels"][0]["category"] == "Bug Fix"
    validate_label_record(row)


def test_validate_label_record_rejects_malformed_records() -> None:
    [valid] = list(iter_labels([{
        "type": "commit",
        "sha": "0123456789abcdef0123456789abcdef01234567",
        "subject": "Fix and refactor tests",
        "body": "",
        "paths": ["tests/test_graph.py"],
    }]))
    validate_label_record(valid)

    mutations = [
        lambda r: r.update(schema="wrong.schema"),
        lambda r: r.update(method="weak-rule-v2"),
        lambda r: r.update(sha=""),
        lambda r: r.update(labels=[]),
        lambda r: r["labels"].append(copy.deepcopy(r["labels"][0])),
        lambda r: r["labels"][0].update(category="Unknown Category"),
        lambda r: r["labels"][0].update(categoryId="wrongId"),
        lambda r: r["labels"][0].update(ruleWeightPercent=True),
        lambda r: r["labels"][0].update(ruleWeightPercent=101),
        lambda r: r["labels"][0].update(ruleWeightPercent=-1),
        lambda r: r["labels"][0].update(status="human_adjudicated"),
        lambda r: r["labels"][0].update(evidence=[]),
        lambda r: r["labels"][1].update(evidenceKinds=["subjectBodyRule"]),
    ]
    for mutate in mutations:
        broken = copy.deepcopy(valid)
        mutate(broken)
        try:
            validate_label_record(broken)
        except ValueError:
            pass
        else:
            raise AssertionError(f"validate_label_record accepted malformed record: {broken!r}")


def test_validate_jsonl_cli_flag_accepts_valid_and_rejects_invalid_files() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        jsonl_path = Path(tmp) / "labels.jsonl"
        [row] = list(iter_labels([{
            "type": "commit",
            "sha": "abc123",
            "subject": "fix bug",
            "body": "",
            "paths": [],
        }]))
        jsonl_path.write_text(json.dumps(row) + "\n", encoding="utf-8")
        assert validate_jsonl_file(jsonl_path) == 1

        ok_proc = subprocess.run(
            [sys.executable, str(REPO_ROOT / "tools/infra/evolution_taxonomy.py"),
             "--validate-jsonl", str(jsonl_path)],
            cwd=REPO_ROOT, capture_output=True, text=True, check=False,
        )
        assert ok_proc.returncode == 0, ok_proc.stderr

        row["labels"][0]["categoryId"] = "corruptedId"
        jsonl_path.write_text(json.dumps(row) + "\n", encoding="utf-8")
        bad_proc = subprocess.run(
            [sys.executable, str(REPO_ROOT / "tools/infra/evolution_taxonomy.py"),
             "--validate-jsonl", str(jsonl_path)],
            cwd=REPO_ROOT, capture_output=True, text=True, check=False,
        )
        assert bad_proc.returncode == 2


def test_category_ids_match_lean_darwin_commit_taxonomy_contract() -> None:
    """Cross-layer Level 5 schema convention contract against DarwinCommitTaxonomy.lean:19-71."""
    lean_src = LEAN_CONTRACT_FILE.read_text(encoding="utf-8")

    # Part 1: 12 ChangeCategory constructors & ChangeCategory.id string literals
    cat_block = re.search(
        r"inductive\s+ChangeCategory\s+where(.*?)deriving\s+Repr,\s*DecidableEq",
        lean_src, re.S,
    )
    assert cat_block is not None, "ChangeCategory inductive block not found"
    lean_constructors = re.findall(r"\|\s*([A-Za-z0-9_]+)", cat_block.group(1))

    id_block = re.search(
        r"def\s+id\s*:\s*ChangeCategory\s*→\s*String(.*?)theorem\s+id_injective",
        lean_src, re.S,
    )
    assert id_block is not None, "ChangeCategory.id definition block not found"
    lean_id_pairs = re.findall(r"\|\s*([A-Za-z0-9_]+)\s*=>\s*\"([^\"]+)\"", id_block.group(1))

    python_category_ids = list(CATEGORY_IDS.values())
    assert len(lean_constructors) == 12
    assert [ctor for ctor, _ in lean_id_pairs] == lean_constructors
    assert [lit for _, lit in lean_id_pairs] == lean_constructors
    assert python_category_ids == lean_constructors
    assert len(set(python_category_ids)) == 12

    # Part 2: ChangeLabelEvidence constructors match EVIDENCE_KINDS
    ev_block = re.search(
        r"inductive\s+ChangeLabelEvidence\s+where(.*?)deriving\s+Repr,\s*DecidableEq",
        lean_src, re.S,
    )
    assert ev_block is not None, "ChangeLabelEvidence inductive block not found"
    lean_ev_constructors = re.findall(r"\|\s*([A-Za-z0-9_]+)", ev_block.group(1))
    assert tuple(lean_ev_constructors) == EVIDENCE_KINDS == (
        "subjectBodyRule",
        "pathHint",
        "defaultNoRuleMatch",
        "other",
    )

    # Part 3: CommitChangeLabel structure fields (Fin 101 weight & List ChangeLabelEvidence)
    label_block = re.search(
        r"structure\s+CommitChangeLabel\s+where(.*?)deriving\s+Repr,\s*DecidableEq",
        lean_src, re.S,
    )
    assert label_block is not None, "CommitChangeLabel structure block not found"
    fields_text = label_block.group(1)
    assert "category : ChangeCategory" in fields_text
    assert "ruleWeightPercent : Fin 101" in fields_text
    assert "evidenceKinds : List ChangeLabelEvidence" in fields_text


def test_gemCategoryIdsMatchLeanDarwinCommitTaxonomyContract() -> None:
    """Level 5 schema convention contract for GEM-related evolution categories (not a logical embedding)."""
    lean_src = LEAN_CONTRACT_FILE.read_text(encoding="utf-8")
    id_block = re.search(
        r"def\s+id\s*:\s*ChangeCategory\s*→\s*String(.*?)theorem\s+id_injective",
        lean_src, re.S,
    )
    assert id_block is not None, "ChangeCategory.id definition block not found"
    lean_id_map = dict(
        re.findall(r"\|\s*([A-Za-z0-9_]+)\s*=>\s*\"([^\"]+)\"", id_block.group(1))
    )
    gem_relevant_categories = {
        "Feature Introduction": "featureIntroduction",
        "Refactor/Restructure": "refactorRestructure",
        "Test Evolution": "testEvolution",
        "Documentation/Developer UX": "documentationDeveloperUx",
    }
    for human_label, expected_id in gem_relevant_categories.items():
        assert CATEGORY_IDS[human_label] == expected_id
        assert lean_id_map.get(expected_id) == expected_id
    assert set(CATEGORY_IDS.values()) == set(lean_id_map.values())
    assert len(CATEGORY_IDS) == len(lean_id_map) == 12
    assert len(GEM_CLADE_IDS) == 10
    assert len(GEM_EPOCH_IDS) == 8
    gem_poset_src = LEAN_GEM_POSET_FILE.read_text(encoding="utf-8")
    for clade_ctor in GEM_CLADE_IDS.values():
        assert clade_ctor in gem_poset_src
    for epoch_ctor in GEM_EPOCH_IDS.values():
        assert epoch_ctor in gem_poset_src


def test_gemEvidenceKindsMatchLeanChangeLabelEvidenceContract() -> None:
    """Level 5 schema convention contract for 4-element ChangeLabelEvidence alignment (not a logical embedding)."""
    lean_src = LEAN_CONTRACT_FILE.read_text(encoding="utf-8")
    ev_block = re.search(
        r"inductive\s+ChangeLabelEvidence\s+where(.*?)deriving\s+Repr,\s*DecidableEq",
        lean_src, re.S,
    )
    assert ev_block is not None, "ChangeLabelEvidence inductive block not found"
    lean_ev_constructors = tuple(
        re.findall(r"\|\s*([A-Za-z0-9_]+)", ev_block.group(1))
    )
    assert len(lean_ev_constructors) == 4
    assert lean_ev_constructors == EVIDENCE_KINDS


class EvolutionTaxonomyUnitTests(unittest.TestCase):
    """Unittest wrapper so `python3 -m unittest tests/test_evolution_taxonomy.py` runs all tests."""

    def test_classify_facets_and_evidence_kinds(self) -> None:
        test_classify_emits_nonhierarchical_facets_with_evidence()

    def test_unmatched_default_label(self) -> None:
        test_unmatched_commit_is_labeled_as_weak_default_not_species()

    def test_streamed_labels_schema(self) -> None:
        test_streamed_labels_have_versioned_schema_and_keep_commit_identity()

    def test_validator_rejects_malformed(self) -> None:
        test_validate_label_record_rejects_malformed_records()

    def test_validate_jsonl_cli(self) -> None:
        test_validate_jsonl_cli_flag_accepts_valid_and_rejects_invalid_files()

    def test_lean_contract_alignment(self) -> None:
        test_category_ids_match_lean_darwin_commit_taxonomy_contract()

    def test_gem_category_ids_contract(self) -> None:
        test_gemCategoryIdsMatchLeanDarwinCommitTaxonomyContract()

    def test_gem_evidence_kinds_contract(self) -> None:
        test_gemEvidenceKindsMatchLeanChangeLabelEvidenceContract()


if __name__ == "__main__":
    unittest.main()

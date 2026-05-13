import json
from pathlib import Path

from tools.infra.generate_translation_dedup_report import build_markdown, build_report


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=True) + "\n" for record in records),
        encoding="utf-8",
    )


def test_generate_translation_dedup_report_separates_exact_scc_and_review(tmp_path: Path) -> None:
    wire_dir = tmp_path / "wire"
    translation_dir = tmp_path / "translation"

    write_jsonl(
        wire_dir / "ig_decl_topologies.jsonl",
        [
            {"decl": "A.uPlus", "patternHash": "sha256:triple", "roleHash": "sha256:plus"},
            {"decl": "A.uMinus", "patternHash": "sha256:triple", "roleHash": "sha256:minus"},
            {"decl": "A.nearOnly", "patternHash": "sha256:other", "roleHash": "sha256:other"},
        ],
    )
    write_jsonl(
        translation_dir / "ig_translation_candidates.jsonl",
        [
            {
                "sourceDecl": "A.uPlus",
                "targetDecl": "A.uMinus",
                "candidateKind": "same_patternHash",
                "verified": True,
                "verificationTier": "derived_canonical_hash",
                "leanVerified": False,
                "reviewOnly": False,
            },
            {
                "sourceDecl": "A.uPlus",
                "targetDecl": "A.uMinus",
                "candidateKind": "lean_kernel_equivalence",
                "verified": True,
                "verificationTier": "lean_kernel",
                "leanVerified": True,
                "reviewOnly": False,
            },
            {
                "sourceDecl": "A.uPlus",
                "targetDecl": "A.nearOnly",
                "candidateKind": "logic_vector_near",
                "verified": False,
                "reviewOnly": True,
                "signals": {"logicVectorCosine": 0.99},
            },
        ],
    )
    write_jsonl(
        translation_dir / "ig_translation_edges.jsonl",
        [
            {
                "sourceDecl": "A.uPlus",
                "targetDecl": "A.uMinus",
                "translationKind": "same_patternHash",
                "kind": "verified_translation",
                "verificationTier": "derived_canonical_hash",
                "leanVerified": False,
            },
            {
                "sourceDecl": "A.uPlus",
                "targetDecl": "A.uMinus",
                "translationKind": "lean_kernel_equivalence",
                "kind": "verified_translation",
                "verificationTier": "lean_kernel",
                "leanVerified": True,
            }
        ],
    )
    write_jsonl(
        translation_dir / "ig_translation_scc.jsonl",
        [
            {
                "memberCount": 2,
                "members": ["A.uPlus", "A.uMinus"],
                "translationSccHash": "sha256:scc",
            }
        ],
    )

    report = build_report(wire_dir, translation_dir)
    markdown = build_markdown(report)

    assert report["stats"]["translation_candidates"] == 3
    assert report["stats"]["verified_candidates"] == 2
    assert report["stats"]["lean_verified_candidates"] == 1
    assert report["stats"]["review_only_candidates"] == 1
    assert report["verified_edge_tier_counts"] == {"derived_canonical_hash": 1, "lean_kernel": 1}
    assert report["exact_buckets"]["patternHash"][0]["declarations"] == ["A.uMinus", "A.uPlus"]
    assert report["verified_translation_sccs"][0]["members"] == ["A.uPlus", "A.uMinus"]
    assert report["top_vector_review_candidates"][0]["targetDecl"] == "A.nearOnly"

    assert "Translation Dedup Report" in markdown
    assert "Verified Translation SCCs" in markdown
    assert "Verification Tiers" in markdown
    assert "Top Vector Review Candidates" in markdown

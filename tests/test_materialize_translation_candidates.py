import json
from pathlib import Path

from tools.infra.materialize_translation_candidates import materialize


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=True) + "\n" for record in records),
        encoding="utf-8",
    )


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def test_translation_candidates_separate_verified_hashes_from_vector_review(tmp_path: Path) -> None:
    wire_dir = tmp_path / "wire"
    vector_dir = tmp_path / "vectors"
    out_dir = tmp_path / "out"

    write_jsonl(
        wire_dir / "ig_decl_topologies.jsonl",
        [
            {
                "_key": "topo_a",
                "decl": "A.uPlus",
                "module": "A",
                "ownerAwareHash": "sha256:ownerA",
                "patternHash": "sha256:triple",
                "roleHash": "sha256:plus",
                "roleHashTokens": [
                    "shape:triple-product",
                    "projectorRole:left:P",
                    "projectorRole:right:P0",
                ],
            },
            {
                "_key": "topo_b",
                "decl": "A.uMinus",
                "module": "A",
                "ownerAwareHash": "sha256:ownerB",
                "patternHash": "sha256:triple",
                "roleHash": "sha256:minus",
                "roleHashTokens": [
                    "shape:triple-product",
                    "projectorRole:left:P0",
                    "projectorRole:right:P",
                ],
            },
            {
                "_key": "topo_c",
                "decl": "A.nearOnly",
                "module": "A",
                "ownerAwareHash": "sha256:ownerC",
                "patternHash": "sha256:other",
                "roleHash": "sha256:other",
                "roleHashTokens": ["shape:other"],
            },
        ],
    )
    write_jsonl(
        vector_dir / "ig_logic_vectors.jsonl",
        [
            {"decl": "A.uPlus", "logicVector": [1.0, 0.0]},
            {"decl": "A.uMinus", "logicVector": [1.0, 0.0]},
            {"decl": "A.nearOnly", "logicVector": [0.99, 0.01]},
        ],
    )

    report = materialize(wire_dir, vector_dir, out_dir, cosine_threshold=0.95)

    candidates = read_jsonl(out_dir / "ig_translation_candidates.jsonl")
    edges = read_jsonl(out_dir / "ig_translation_edges.jsonl")
    sccs = read_jsonl(out_dir / "ig_translation_scc.jsonl")

    assert report["counts"]["ig_translation_candidates"] >= 1
    same_pattern = [
        row for row in candidates
        if row["sourceDecl"] == "A.uPlus"
        and row["targetDecl"] == "A.uMinus"
        and row["candidateKind"] == "same_patternHash"
    ]
    assert same_pattern
    assert same_pattern[0]["verified"] is True
    assert same_pattern[0]["verificationTier"] == "derived_canonical_hash"
    assert same_pattern[0]["leanVerified"] is False
    assert same_pattern[0]["reviewOnly"] is False
    assert same_pattern[0]["safeForDerivedSCC"] is True
    assert same_pattern[0]["safeForAutoRewrite"] is False

    role_swap = [
        row for row in candidates
        if row["sourceDecl"] == "A.uPlus"
        and row["targetDecl"] == "A.uMinus"
        and row["candidateKind"] == "role_swap"
    ]
    assert role_swap
    assert role_swap[0]["verified"] is True
    assert role_swap[0]["verificationTier"] == "derived_role_token"
    assert role_swap[0]["leanVerified"] is False

    vector_only = [
        row for row in candidates
        if row["sourceDecl"] == "A.uPlus"
        and row["targetDecl"] == "A.nearOnly"
        and row["candidateKind"] == "logic_vector_near"
    ]
    assert vector_only
    assert vector_only[0]["verified"] is False
    assert vector_only[0]["verificationTier"] == "vector_review"
    assert vector_only[0]["leanVerified"] is False
    assert vector_only[0]["reviewOnly"] is True

    assert all(edge["kind"] == "verified_translation" for edge in edges)
    assert all(edge["safeForDedupSCC"] is True for edge in edges)
    assert all(edge["safeForAutoRewrite"] is False for edge in edges)
    assert all(edge["leanVerified"] is False for edge in edges)
    assert any({"A.uPlus", "A.uMinus"}.issubset(set(row["members"])) for row in sccs)


def test_translation_candidates_promote_only_certificate_rows_to_lean_verified(tmp_path: Path) -> None:
    wire_dir = tmp_path / "wire"
    vector_dir = tmp_path / "vectors"
    out_dir = tmp_path / "out"
    certs = tmp_path / "lean_equiv.jsonl"

    write_jsonl(
        wire_dir / "ig_decl_topologies.jsonl",
        [
            {"_key": "topo_a", "decl": "A.left", "module": "A", "patternHash": "sha256:left"},
            {"_key": "topo_b", "decl": "A.right", "module": "A", "patternHash": "sha256:right"},
        ],
    )
    write_jsonl(vector_dir / "ig_logic_vectors.jsonl", [])
    write_jsonl(
        certs,
        [
            {
                "sourceDecl": "A.left",
                "targetDecl": "A.right",
                "leanVerified": True,
                "certificateHash": "sha256:kernel",
                "certificatePath": "reports/kernel/A.left_A.right.json",
                "verificationTier": "lean_kernel_type_defeq",
                "safeForAutoRewrite": True,
            },
            {
                "sourceDecl": "A.right",
                "targetDecl": "A.left",
                "kernelVerified": False,
                "certificateHash": "sha256:not-used",
            },
        ],
    )

    materialize(
        wire_dir,
        vector_dir,
        out_dir,
        cosine_threshold=0.95,
        lean_equivalence_certs=certs,
    )

    candidates = read_jsonl(out_dir / "ig_translation_candidates.jsonl")
    edges = read_jsonl(out_dir / "ig_translation_edges.jsonl")

    lean_candidates = [row for row in candidates if row["candidateKind"] == "lean_kernel_equivalence"]
    assert len(lean_candidates) == 1
    assert lean_candidates[0]["sourceDecl"] == "A.left"
    assert lean_candidates[0]["targetDecl"] == "A.right"
    assert lean_candidates[0]["leanVerified"] is True
    assert lean_candidates[0]["verificationTier"] == "lean_kernel_type_defeq"
    assert lean_candidates[0]["safeForAutoRewrite"] is True

    lean_edges = [row for row in edges if row["translationKind"] == "lean_kernel_equivalence"]
    assert len(lean_edges) == 1
    assert lean_edges[0]["leanVerified"] is True
    assert lean_edges[0]["proofAuthority"] == "lean-kernel-certificate"
    assert lean_edges[0]["safeForAutoRewrite"] is True


def test_translation_candidates_respects_certificate_rewrite_flag(tmp_path: Path) -> None:
    wire_dir = tmp_path / "wire"
    vector_dir = tmp_path / "vectors"
    out_dir = tmp_path / "out"
    certs = tmp_path / "lean_equiv.jsonl"

    write_jsonl(
        wire_dir / "ig_decl_topologies.jsonl",
        [
            {"_key": "topo_a", "decl": "A.left", "module": "A", "patternHash": "sha256:left"},
            {"_key": "topo_b", "decl": "A.right", "module": "A", "patternHash": "sha256:right"},
        ],
    )
    write_jsonl(vector_dir / "ig_logic_vectors.jsonl", [])
    write_jsonl(
        certs,
        [
            {
                "sourceDecl": "A.left",
                "targetDecl": "A.right",
                "leanVerified": True,
                "verificationTier": "lean_kernel_type_defeq",
                "safeForAutoRewrite": False,
            },
        ],
    )

    materialize(
        wire_dir,
        vector_dir,
        out_dir,
        cosine_threshold=0.95,
        lean_equivalence_certs=certs,
    )

    lean_edges = [
        row
        for row in read_jsonl(out_dir / "ig_translation_edges.jsonl")
        if row["translationKind"] == "lean_kernel_equivalence"
    ]
    assert len(lean_edges) == 1
    assert lean_edges[0]["leanVerified"] is True
    assert lean_edges[0]["safeForAutoRewrite"] is False

import json
import subprocess
from pathlib import Path


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def read_jsonl(path: Path) -> list[dict]:
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def test_kernel_equivalence_export_promotes_only_isdefeq_pairs(tmp_path: Path) -> None:
    pairs = tmp_path / "pairs.jsonl"
    out = tmp_path / "certs.jsonl"
    prefix = "DAG.KernelEquivalenceFixture"
    write_jsonl(
        pairs,
        [
            {"sourceDecl": f"{prefix}.trueA", "targetDecl": f"{prefix}.trueB"},
            {"sourceDecl": f"{prefix}.twoA", "targetDecl": f"{prefix}.twoB"},
            {"sourceDecl": f"{prefix}.twoA", "targetDecl": f"{prefix}.three"},
            {"sourceDecl": f"{prefix}.missing", "targetDecl": f"{prefix}.twoA"},
        ],
    )

    subprocess.run(
        ["lake", "build", "DAG.KernelEquivalenceFixture"],
        check=True,
        cwd=Path(__file__).resolve().parents[1],
    )
    subprocess.run(
        [
            "lake",
            "env",
            "lean",
            "--run",
            "lean/DAG/KernelEquivalenceExport.lean",
            "DAG.KernelEquivalenceFixture",
            str(pairs),
            str(out),
            "--mode",
            "type-and-value",
        ],
        check=True,
        cwd=Path(__file__).resolve().parents[1],
    )

    rows = {(row["sourceDecl"], row["targetDecl"]): row for row in read_jsonl(out)}

    true_pair = rows[(f"{prefix}.trueA", f"{prefix}.trueB")]
    assert true_pair["kernelTypeDefEq"] is True
    assert true_pair["kernelValueDefEq"] is True
    assert true_pair["leanVerified"] is True
    assert true_pair["safeForAutoRewrite"] is True
    assert true_pair["verificationTier"] == "lean_kernel_type_and_value_defeq"
    assert true_pair["proofAuthority"] == "lean-kernel-isDefEq"

    two_pair = rows[(f"{prefix}.twoA", f"{prefix}.twoB")]
    assert two_pair["kernelTypeDefEq"] is True
    assert two_pair["kernelValueDefEq"] is True
    assert two_pair["leanVerified"] is True

    three_pair = rows[(f"{prefix}.twoA", f"{prefix}.three")]
    assert three_pair["kernelTypeDefEq"] is True
    assert three_pair["kernelValueDefEq"] is False
    assert three_pair["leanVerified"] is False
    assert three_pair["safeForAutoRewrite"] is False

    missing_pair = rows[(f"{prefix}.missing", f"{prefix}.twoA")]
    assert missing_pair["sourceFound"] is False
    assert missing_pair["targetFound"] is True
    assert missing_pair["leanVerified"] is False
    assert missing_pair["error"] == "source declaration not found"

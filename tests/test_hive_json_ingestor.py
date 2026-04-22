import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
TOOL = REPO / "tools" / "infra" / "ingest_hive_json.py"


def test_ingest_hive_json_normalizes_and_hashes_packets(tmp_path: Path) -> None:
    input_path = tmp_path / "hive.log"
    input_path.write_text(
        "\n".join(
            [
                "warning: ignored",
                'HIVE_JSON {"artifactKind":"InfoTreeArtifact","space":"infotree","module":"Demo","goalIndex":0,"targetPretty":"P → P","canonicalPreimage":"(forall (bvar 0) (bvar 1))","targetHashShapeCanonical":"(forall (bvar 0) (bvar 1))","normalizationPolicy":"instantiateMVars+whnf(default)","fvarPolicy":"used-fvars-in-local-context-order","hasUnassignedMVars":false,"unabstractedFVars":[]}',
                'HIVE_JSON {"artifactKind":"DiamondFossil","space":"logos","constName":"And.intro","declarationKind":"constructor","fullTypePretty":"forall {a : Prop} {b : Prop}, a -> b -> And a b","conclusionPretty":"And _uniq.18 _uniq.19","fullTypeHashShapeCanonical":"(forall ...)","conclusionHashShapeCanonical":"(app (app (const And) (bvar 1)) (bvar 0))","kernelStatus":"verified"}',
            ]
        ),
        encoding="utf-8",
    )
    out_path = tmp_path / "hive.jsonl"
    manifest_path = tmp_path / "manifest.json"

    subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--input",
            str(input_path),
            "--out",
            str(out_path),
            "--manifest",
            str(manifest_path),
            "--source",
            "unit-test",
        ],
        cwd=REPO,
        check=True,
        text=True,
        capture_output=True,
    )

    records = [json.loads(line) for line in out_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    assert len(records) == 2
    assert records[0]["schema"] == "info_geometry.hive_memory.v1"
    assert records[0]["artifact_kind"] == "InfoTreeArtifact"
    assert records[0]["entity_key"] == "Demo:0"
    assert records[0]["canonical_shape"] == "(forall (bvar 0) (bvar 1))"
    assert len(records[0]["packet_sha256"]) == 64
    assert len(records[0]["shape_sha256"]) == 64
    assert records[1]["entity_key"] == "And.intro"
    assert records[1]["canonical_shape"] == "(app (app (const And) (bvar 1)) (bvar 0))"
    assert manifest["record_count"] == 2
    assert manifest["source"] == "unit-test"


def test_ingest_hive_json_from_real_lean_output(tmp_path: Path) -> None:
    source_path = tmp_path / "HiveSmoke.lean"
    source_path.write_text(
        "\n".join(
            [
                "import Mathlib",
                "import InfoGeometry.Meta.HiveLogos",
                "",
                "example (P Q : Prop) : P -> P := by",
                "  hive_probe",
                "  intro h",
                "  exact h",
                "",
                "#hive_index_decl And.intro",
            ]
        ),
        encoding="utf-8",
    )

    lean = subprocess.run(
        ["bash", "-lc", f'export PATH="$HOME/.elan/bin:$PATH"; lake env lean {source_path}'],
        cwd=REPO,
        check=True,
        text=True,
        capture_output=True,
    )
    out_path = tmp_path / "real.jsonl"

    subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--out",
            str(out_path),
            "--source",
            "lean-smoke",
        ],
        cwd=REPO,
        input=lean.stdout,
        check=True,
        text=True,
        capture_output=True,
    )

    records = [json.loads(line) for line in out_path.read_text(encoding="utf-8").splitlines() if line.strip()]

    assert [record["artifact_kind"] for record in records] == ["InfoTreeArtifact", "DiamondFossil"]
    assert records[0]["packet"]["module"] == "_stdin"
    assert records[1]["packet"]["constName"] == "And.intro"
    assert records[1]["canonical_shape"] == records[1]["packet"]["conclusionHashShapeCanonical"]

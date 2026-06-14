from pathlib import Path

import pytest

from tools.infra import arango_causal_memory as acm


def test_local_attention_uses_dag_rows(tmp_path: Path) -> None:
    index = tmp_path / "index"
    index.mkdir()
    (index / "decls.jsonl").write_text(
        '{"name":"InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights",'
        '"kind":"def","module":"InfoGeometry.LLM.KreinAttentionEnergy",'
        '"file":"lean/InfoGeometry/LLM/KreinAttentionEnergy.lean","line":26}\n'
        '{"name":"InfoGeometry.Topology.Delaunay.flip_inverse_identity",'
        '"kind":"theorem","module":"InfoGeometry.Topology.DelaunayFlipMatrix",'
        '"file":"lean/InfoGeometry/Topology/DelaunayFlipMatrix.lean","line":23}\n',
        encoding="utf-8",
    )
    (index / "edges.jsonl").write_text(
        '{"src":"InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights",'
        '"dst":"InfoGeometry.Canonical.Attention.attentionWeights","kind":"value"}\n',
        encoding="utf-8",
    )

    out = acm.local_attention("Krein attention", index_dir=index, limit=2, depth=1)

    assert out["source"] == "artifacts/dag/index/{decls,edges}.jsonl"
    assert out["hits"][0]["name"] == "InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights"
    assert out["hits"][0]["neighborhood"]["edges"][0]["dst"] == "InfoGeometry.Canonical.Attention.attentionWeights"


def test_projection_preflight_requires_explicit_acknowledgement() -> None:
    with pytest.raises(SystemExit) as exc:
        acm.main(["preflight", "--name", "InfoGeometry.X"])
    assert "projection cache" in str(exc.value)


def test_projection_attention_requires_explicit_acknowledgement() -> None:
    with pytest.raises(SystemExit) as exc:
        acm.main(["attention-preflight", "--prompt-embedding", "[1.0]"])
    assert "projection cache" in str(exc.value)

import copy
import hashlib
import json
import sys

import pytest

torch = pytest.importorskip("torch")

from tests.test_train_taxonomy_baseline import _fixtures
from tools.repository_evolution.context_transport import build_context_transport


def test_context_balance_joint_marginals_and_relabeling():
    source_map, _, packet = _fixtures()
    ids = [row["artifactId"] for row in packet["embeddings"][:3]]
    result = build_context_transport(source_map, packet, ids)
    weights = torch.tensor(result["coupling"], dtype=torch.float64)
    joint = torch.tensor(result["jointDistribution"], dtype=torch.float64)
    assert torch.allclose(weights.sum(0), torch.ones(3, dtype=torch.float64))
    assert torch.allclose(weights.sum(1), torch.ones(3, dtype=torch.float64))
    assert joint.sum().item() == pytest.approx(1)
    assert torch.allclose(joint.sum(0), joint.sum(1))
    reordered = build_context_transport(source_map, packet, ids[::-1])
    assert torch.allclose(torch.tensor(reordered["coupling"], dtype=torch.float64),
                          weights.flip((0, 1)))
    assert result["sourceEmbeddingPacketSha256"] == packet["packetSha256"]


def test_context_rejects_corruption_duplicates_and_unbounded_selection():
    source_map, _, packet = _fixtures()
    ids = [row["artifactId"] for row in packet["embeddings"][:3]]
    with pytest.raises(ValueError, match="max_context_size"):
        build_context_transport(source_map, packet, ids, max_context_size=2)
    with pytest.raises(ValueError, match="duplicate"):
        build_context_transport(source_map, packet, [ids[0], ids[0]])
    corrupted = copy.deepcopy(packet)
    corrupted["embeddings"][0]["vector"][0] += 1
    with pytest.raises(ValueError, match="digest"):
        build_context_transport(source_map, corrupted, ids)


def test_insufficient_iterations_are_not_reported_as_bistochastic():
    source_map, _, packet = _fixtures()
    ids = [row["artifactId"] for row in packet["embeddings"][:3]]
    with pytest.raises(ValueError, match="did not converge"):
        build_context_transport(source_map, packet, ids, iterations=1)


def test_cli_exports_and_rejects_changed_live_source(tmp_path, monkeypatch):
    from tools.repository_evolution.context_transport import main
    from tools.repository_evolution.latent_taxonomy import build_encoder_embedding_packet

    source_map, _, packet = _fixtures()
    for file_row, embedding in zip(source_map["files"], packet["embeddings"]):
        path = tmp_path / file_row["path"]
        path.parent.mkdir(parents=True, exist_ok=True)
        content = file_row["path"].encode()
        path.write_bytes(content)
        digest = hashlib.sha256(content).hexdigest()
        file_row["contentSha256"] = digest
        embedding["sourceSha256"] = digest
    packet = build_encoder_embedding_packet(
        source_map, packet["encoderVersion"], packet["embeddings"],
        encoder_training=packet["encoderTraining"],
    )
    map_path, packet_path, output = [tmp_path / name for name in (
        "map.json", "embeddings.json", "coupling.json")]
    map_path.write_text(json.dumps(source_map))
    packet_path.write_text(json.dumps(packet))
    artifact = packet["embeddings"][0]["artifactId"]
    monkeypatch.setattr(sys, "argv", ["context_transport", str(map_path), str(packet_path),
        "--artifact", artifact, "--repo-root", str(tmp_path), "--out", str(output)])
    assert main() == 0
    exported = output.read_bytes()
    assert json.loads(exported)["coupling"] == [[1.0]]
    (tmp_path / artifact).write_text("changed source")
    with pytest.raises(ValueError, match="digest differs"):
        main()
    assert output.read_bytes() == exported

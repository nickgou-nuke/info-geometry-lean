from __future__ import annotations

from tools.leantrail.critic_packets import PacketIndex, generate_for_node


def _node(name: str) -> dict:
    return {
        "id": name,
        "name": name,
        "kind": "Declaration",
        "module": "Test.Module",
        "file": "Test/Module.lean",
        "line": 1,
        "role": "unknown",
        "attrs": {
            "contamination": {"state": "clean"},
        },
    }


def _empty_index() -> PacketIndex:
    return PacketIndex({}, {}, {})


def test_generated_helper_decl_names_do_not_emit_critic_packets() -> None:
    names = [
        "Test.EmergentVolumeWitness.mk",
        "Test.EmergentVolumeWitness.mk.inj",
        "Test.EmergentVolumeWitness.casesOn",
        "Test.EmergentVolumeWitness.ctorIdx",
        "Test.EmergentVolumeWitness.noConfusion",
        "Test.EmergentVolumeWitness.noConfusionType",
        "Test.EmergentVolumeWitness.rec",
        "Test.EmergentVolumeWitness.recOn",
        "Test.EmergentVolumeWitness.mk.sizeOf_spec",
    ]

    for name in names:
        assert generate_for_node(_node(name), _empty_index()) == []


def test_primary_witness_surface_still_emits_obfuscation_packet() -> None:
    packets = generate_for_node(_node("Test.EmergentVolumeWitness"), _empty_index())
    assert any(packet["critic_kind"] == "obfuscation_suspicion" for packet in packets)

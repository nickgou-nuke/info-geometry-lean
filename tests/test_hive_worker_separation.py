import unittest

from tools.infra import hive_arango_queue as queue_tool
from tools.infra import hive_audit_worker
from tools.infra import hive_promotion_worker


def passing_audit_packet(**updates):
    packet = {
        "schema": "hive.packet.audit.v1",
        "authority": "audit_checked",
        "representation_class": "owner",
        "representation_depth": "operatorial",
        "build_key": "build-1",
        "verdict": "pass",
        "producer_worker_id": "builder-1",
        "auditor_worker_id": "auditor-1",
        "worker_id": "auditor-1",
        "promotion_allowed": True,
    }
    packet.update(updates)
    return packet


class HiveWorkerSeparationTests(unittest.TestCase):
    def test_audit_build_rejects_missing_or_reused_worker_ids(self):
        build = {
            "authority": "build_checked",
            "state": "passed",
            "representation_class": "owner",
            "packet_key": "build-1",
            "worker_id": "builder-1",
        }
        verification = {"authority": "lean_checked", "source_regime": "theorem_lane"}

        distinct_verdict, _ = hive_audit_worker.audit_build(
            build, verification, {"proposal": {"backend_kind": "unknown"}},
            auditor_worker_id="auditor-1",
        )
        reused_verdict, reused_findings = hive_audit_worker.audit_build(
            build, verification, {"proposal": {"backend_kind": "unknown"}},
            auditor_worker_id="builder-1",
        )
        missing_verdict, _ = hive_audit_worker.audit_build(
            {**build, "worker_id": None}, verification,
            {"proposal": {"backend_kind": "unknown"}}, auditor_worker_id="auditor-1",
        )
        missing_lineage_verdict, _ = hive_audit_worker.audit_build(
            build, verification, {}, auditor_worker_id="auditor-1"
        )

        self.assertEqual(distinct_verdict, "pass")
        self.assertEqual(reused_verdict, "fail")
        self.assertTrue(any("must be distinct" in item for item in reused_findings))
        self.assertEqual(missing_verdict, "fail")
        self.assertEqual(missing_lineage_verdict, "conditional_pass")

    def test_passing_audit_packet_requires_distinct_bound_ids(self):
        valid = passing_audit_packet()
        validated = queue_tool.validate_packet_invariants(valid)
        self.assertEqual(validated["producer_worker_id"], "builder-1")
        self.assertEqual(validated["auditor_worker_id"], "auditor-1")

        invalid_packets = (
            passing_audit_packet(producer_worker_id=""),
            passing_audit_packet(producer_worker_id="auditor-1"),
            passing_audit_packet(worker_id="other-auditor"),
        )
        for packet in invalid_packets:
            with self.subTest(packet=packet):
                with self.assertRaises(ValueError):
                    queue_tool.validate_packet_invariants(packet)

    def test_audit_packet_producer_id_must_match_referenced_build(self):
        original_fetch = queue_tool.fetch_packet_by_key
        queue_tool.fetch_packet_by_key = lambda *args, **kwargs: {
            "authority": "build_checked", "worker_id": "actual-builder"
        }
        try:
            with self.assertRaisesRegex(ValueError, "does not match referenced BuildPacket"):
                queue_tool.validate_packet_database_invariants(
                    "endpoint", "db", "user", "password",
                    packet=passing_audit_packet(producer_worker_id="claimed-builder"),
                )
        finally:
            queue_tool.fetch_packet_by_key = original_fetch

    def test_promotion_requires_three_distinct_workers_even_with_override(self):
        audit = {
            "verdict": "pass",
            "verification_origin": "theorem_lane",
            "promotion_allowed": True,
            "producer_worker_id": "builder-1",
            "auditor_worker_id": "auditor-1",
            "worker_id": "auditor-1",
        }
        decision, _ = hive_promotion_worker.decide_promotion(
            audit, allow_override=True, promotion_worker_id="promoter-1"
        )
        reused_decision, reused_reasons = hive_promotion_worker.decide_promotion(
            audit, allow_override=True, promotion_worker_id="builder-1"
        )
        self.assertEqual(decision, "promote")
        self.assertEqual(reused_decision, "hold")
        self.assertTrue(any("must be distinct" in item for item in reused_reasons))

    def test_promotion_override_cannot_bypass_audit_permission(self):
        audit = {
            "verdict": "pass",
            "verification_origin": "theorem_lane",
            "promotion_allowed": False,
            "producer_worker_id": "builder-1",
            "auditor_worker_id": "auditor-1",
            "worker_id": "auditor-1",
        }
        decision, reasons = hive_promotion_worker.decide_promotion(
            audit, allow_override=True, promotion_worker_id="promoter-1"
        )
        self.assertEqual(decision, "hold")
        self.assertTrue(any("does not allow promotion" in item for item in reasons))

    def test_promotion_packet_schema_requires_distinct_roles(self):
        packet = {
            "schema": "hive.packet.promotion_decision.v1",
            "authority": "promoted",
            "representation_class": "owner",
            "representation_depth": "operatorial",
            "audit_key": "audit-1",
            "decision": "promote",
            "producer_worker_id": "builder-1",
            "auditor_worker_id": "auditor-1",
            "promotion_worker_id": "promoter-1",
            "worker_id": "promoter-1",
        }
        validated = queue_tool.validate_packet_invariants(packet)
        self.assertEqual(validated["promotion_worker_id"], "promoter-1")
        with self.assertRaisesRegex(ValueError, "must be distinct"):
            queue_tool.validate_packet_invariants({**packet, "promotion_worker_id": "builder-1", "worker_id": "builder-1"})

    def test_promotion_database_invariant_binds_copied_roles_to_audit(self):
        original_fetch = queue_tool.fetch_packet_by_key
        queue_tool.fetch_packet_by_key = lambda *args, **kwargs: {
            "authority": "audit_checked",
            "verdict": "pass",
            "promotion_allowed": True,
            "producer_worker_id": "builder-1",
            "auditor_worker_id": "auditor-1",
            "worker_id": "auditor-1",
        }
        packet = {
            "schema": "hive.packet.promotion_decision.v1",
            "audit_key": "audit-1",
            "decision": "promote",
            "producer_worker_id": "builder-1",
            "auditor_worker_id": "auditor-1",
            "promotion_worker_id": "promoter-1",
            "worker_id": "promoter-1",
        }
        try:
            for field, value, message in (
                ("producer_worker_id", "forged-builder", "producer_worker_id"),
                ("auditor_worker_id", "forged-auditor", "auditor_worker_id"),
            ):
                with self.subTest(field=field):
                    with self.assertRaisesRegex(ValueError, message):
                        queue_tool.validate_packet_database_invariants(
                            "endpoint", "db", "user", "password",
                            packet={**packet, field: value},
                        )
        finally:
            queue_tool.fetch_packet_by_key = original_fetch


if __name__ == "__main__":
    unittest.main()

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from types import SimpleNamespace
from pathlib import Path
from unittest.mock import patch

from tools.infra.opengauss_ground_truth_contract import (
    canonical_digest,
    validate_contract_payload,
)
from tools.infra.hive_packet_validate import validate_ground_truth_candidate_integrity
from tools.infra.hive_packet_build import build_theorem_candidate
from tools.infra.opengauss_cli import discover_declarations
from tools.infra.opengauss_cli import main as opengauss_main
from tools.infra.opengauss_ground_truth_contract import validate_draft_receipt_payload
from tools.infra.pantograph_epistemic_swarm import CandidatePacket


class GroundTruthContractTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        owner = self.root / "lean" / "Owner.lean"
        owner.parent.mkdir(parents=True)
        self.owner_text = (
            "namespace Demo\n"
            "/-- theorem base : False := by trivial -/\n"
            "theorem base : True := by trivial\n"
            "end Demo\n"
        )
        owner.write_text(self.owner_text, encoding="utf-8")
        source_hash = hashlib.sha256(owner.read_bytes()).hexdigest()
        report = {
            "schema": "info_geometry.opengauss.discovery_report.v1",
            "authority": "navigation_only",
            "graph_is_proof_authority": False,
            "query": "base",
            "carriers_found": [],
            "lemmas_found": [
                {
                    "name": "base", "qualified_name": "Demo.base", "kind": "theorem",
                    "file": "lean/Owner.lean", "source_sha256": source_hash,
                    "line": 3, "source_end_line": 3,
                    "lean_statement": "theorem base : True",
                }
            ],
            "recommended_imports": ["Owner"],
            "deduplication_warnings": [],
            "local_dag_context": None,
            "dag_context": None,
        }
        self.receipt = self.root / "artifacts" / "discovery.json"
        self.receipt.parent.mkdir(parents=True)
        self.receipt.write_text(json.dumps(report, sort_keys=True), encoding="utf-8")
        self.receipt_hash = hashlib.sha256(self.receipt.read_bytes()).hexdigest()
        self.contract = {
            "schema": "info_geometry.opengauss.ground_truth_theorem_contract.v1",
            "contract_id": "gtc-demo-1",
            "semantic_status": "human_asserted_not_kernel_verified",
            "claim": "The candidate theorem has type True.",
            "carrier": {
                "type": "Prop",
                "operations": ["logical implication"],
                "conventions": ["Lean proposition equality"],
            },
            "owner_declarations": [
                {
                    "qualified_name": "Demo.base",
                    "kind": "theorem",
                    "source_path": "lean/Owner.lean",
                    "source_sha256": source_hash,
                    "source_line": 3,
                    "source_end_line": 3,
                    "source_excerpt": "theorem base : True := by trivial",
                    "lean_statement": "theorem base : True",
                    "status_assertion": "asserted_proved",
                }
            ],
            "imports": ["Mathlib"],
            "consumers": ["Demo.downstream"],
            "smallest_gap": {
                "declaration_name": "Demo.next",
                "lean_signature": ": True",
                "pantograph_expression": "True",
                "description": "A source-confirmed target gap.",
            },
            "out_of_scope": ["No broader semantic claim is established."],
            "discovery_receipt": {
                "path": "artifacts/discovery.json",
                "sha256": self.receipt_hash,
                "query": "base",
            },
        }

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_validates_source_excerpt_declaration_and_receipt_binding(self) -> None:
        result = validate_contract_payload(self.contract, repo_root=self.root)
        self.assertEqual(result["contract_id"], "gtc-demo-1")
        self.assertEqual(result["missing_declaration_name"], "Demo.next")
        self.assertEqual(result["contract_sha256"], canonical_digest(self.contract))

    def test_rejects_invented_qualified_declaration(self) -> None:
        contract = json.loads(json.dumps(self.contract))
        contract["owner_declarations"][0]["qualified_name"] = "Other.base"
        with self.assertRaisesRegex(ValueError, "no declaration head"):
            validate_contract_payload(contract, repo_root=self.root)

    def test_rejects_statement_not_in_the_quoted_source_excerpt(self) -> None:
        contract = json.loads(json.dumps(self.contract))
        contract["owner_declarations"][0]["lean_statement"] = "theorem base : False"
        with self.assertRaisesRegex(ValueError, "differs from the parsed declaration header"):
            validate_contract_payload(contract, repo_root=self.root)

    def test_rejects_comment_text_as_the_cited_declaration_range(self) -> None:
        contract = json.loads(json.dumps(self.contract))
        declaration = contract["owner_declarations"][0]
        declaration["source_excerpt"] = "theorem base : False := by trivial"
        declaration["lean_statement"] = "theorem base : False"
        with self.assertRaisesRegex(ValueError, "does not equal the cited declaration source range"):
            validate_contract_payload(contract, repo_root=self.root)

    def test_rejects_stale_owner_snapshot(self) -> None:
        (self.root / "lean" / "Owner.lean").write_text(self.owner_text + "-- changed\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "stale source hash"):
            validate_contract_payload(self.contract, repo_root=self.root)

    def test_rejects_receipt_without_the_cited_owner_hit(self) -> None:
        report = json.loads(self.receipt.read_text(encoding="utf-8"))
        report["lemmas_found"] = []
        self.receipt.write_text(json.dumps(report, sort_keys=True), encoding="utf-8")
        self.contract["discovery_receipt"]["sha256"] = hashlib.sha256(self.receipt.read_bytes()).hexdigest()
        with self.assertRaisesRegex(ValueError, "does not contain the cited"):
            validate_contract_payload(self.contract, repo_root=self.root)

    def test_rejects_receipt_hit_at_wrong_line_or_kind(self) -> None:
        report = json.loads(self.receipt.read_text(encoding="utf-8"))
        report["lemmas_found"][0]["line"] = 2
        report["lemmas_found"][0]["kind"] = "def"
        self.receipt.write_text(json.dumps(report, sort_keys=True), encoding="utf-8")
        self.contract["discovery_receipt"]["sha256"] = hashlib.sha256(self.receipt.read_bytes()).hexdigest()
        with self.assertRaisesRegex(ValueError, "does not contain the cited"):
            validate_contract_payload(self.contract, repo_root=self.root)

    def test_rejects_wrong_declaration_kind_in_contract(self) -> None:
        contract = json.loads(json.dumps(self.contract))
        contract["owner_declarations"][0]["kind"] = "def"
        with self.assertRaisesRegex(ValueError, "kind.*differs"):
            validate_contract_payload(contract, repo_root=self.root)

    def test_discovery_does_not_emit_comment_only_declarations(self) -> None:
        decoy = self.root / "lean" / "InfoGeometry" / "Decoy.lean"
        decoy.parent.mkdir(parents=True, exist_ok=True)
        decoy.write_text("/- theorem phantom : False := by trivial -/\n", encoding="utf-8")
        report = discover_declarations("phantom", repo_root=self.root)
        self.assertEqual(report.lemmas_found, [])

    def test_private_declaration_is_not_claimed_under_its_public_name(self) -> None:
        owner = self.root / "lean" / "Owner.lean"
        owner.write_text("namespace Demo\nprivate theorem base : True := by trivial\nend Demo\n", encoding="utf-8")
        from tools.infra.opengauss_ground_truth_contract import _qualified_declaration_heads
        self.assertEqual(_qualified_declaration_heads(owner.read_text(encoding="utf-8")), {})

    def test_unavailable_graph_is_explicitly_accepted_but_invalid_packet_rejected(self) -> None:
        report = json.loads(self.receipt.read_text(encoding="utf-8"))
        report["local_dag_context"] = {
            "status": "unavailable", "authority": "navigation_only",
            "freshness": "unknown", "graph_is_proof_authority": False,
        }
        self.receipt.write_text(json.dumps(report, sort_keys=True), encoding="utf-8")
        self.contract["discovery_receipt"]["sha256"] = hashlib.sha256(self.receipt.read_bytes()).hexdigest()
        validate_contract_payload(self.contract, repo_root=self.root)
        report["local_dag_context"]["status"] = "invalid_packet"
        report["local_dag_context"]["validation_error"] = "bad schema"
        self.receipt.write_text(json.dumps(report, sort_keys=True), encoding="utf-8")
        self.contract["discovery_receipt"]["sha256"] = hashlib.sha256(self.receipt.read_bytes()).hexdigest()
        with self.assertRaisesRegex(ValueError, "invalid local_dag_context"):
            validate_contract_payload(self.contract, repo_root=self.root)

    def test_schema_rejects_unrecorded_import_or_consumer_scope(self) -> None:
        contract = json.loads(json.dumps(self.contract))
        contract["imports"] = []
        with self.assertRaisesRegex(ValueError, "contract schema violation"):
            validate_contract_payload(contract, repo_root=self.root)

    def test_candidate_integrity_binds_gap_signature_and_contract_digest(self) -> None:
        draft_path = self.root / "lean" / "Draft.lean"
        draft_path.write_text(
            "namespace Demo\ntheorem next : True := by trivial\nend Demo\n",
            encoding="utf-8",
        )
        draft_receipt = {
            "schema": "info_geometry.opengauss.contract_bound_draft.v1",
            "contract": self.contract,
            "contract_sha256": canonical_digest(self.contract),
            "source_path": "lean/Draft.lean",
            "source_sha256": hashlib.sha256(draft_path.read_bytes()).hexdigest(),
            "target_name": "Demo.next",
            "declaration_signature": "theorem next : True",
            "target_expression": "True",
        }
        validate_draft_receipt_payload(draft_receipt, repo_root=self.root)
        binding = {
            "contract": self.contract,
            "contract_sha256": canonical_digest(self.contract),
        }
        packet = {
            "kind": "TheoremCandidatePacket",
            "lineage_id": "lineage-demo",
            "symbolic_origin_refs": ["source:demo"],
            "formal_target": {
                "target_name": "Demo.next",
                "target_expression": "True",
                "source_path": "lean/Draft.lean",
                "source_snapshot_sha256": draft_receipt["source_sha256"],
            },
            "draft_binding": {
                "receipt": draft_receipt,
                "receipt_sha256": canonical_digest(draft_receipt),
            },
            "pantograph_binding": {
                "source_path": "lean/Draft.lean",
                "source_snapshot_sha256": draft_receipt["source_sha256"],
                "target_expression": "True",
            },
            "bridge_claim": "Source-grounded candidate target.",
            "novelty_defense": {"summary": "No novelty claim."},
            "repo_anchor_refs": ["lean/Owner.lean"],
            "candidate_dependencies": ["Demo.base"],
            "admissibility_state": "candidate",
            "cost_class": "small",
            "ground_truth_contract": binding,
        }
        material = {
            key: packet[key]
            for key in (
                "kind", "lineage_id", "symbolic_origin_refs", "formal_target",
                "bridge_claim", "novelty_defense", "repo_anchor_refs",
                "candidate_dependencies", "admissibility_state", "cost_class",
                "ground_truth_contract", "draft_binding", "pantograph_binding",
            )
        }
        packet["packet_hash"] = "sha256:" + hashlib.sha256(
            json.dumps(material, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        ).hexdigest()[:32]

        with patch("tools.infra.hive_packet_validate.ROOT", self.root):
            self.assertEqual(validate_ground_truth_candidate_integrity(packet), [])
            self.assertEqual(CandidatePacket.from_dict(packet).formal_target, "True")
            packet["formal_target"]["target_expression"] = ": False"
            errors = validate_ground_truth_candidate_integrity(packet)
        self.assertTrue(any("expression" in error for error in errors))
        self.assertTrue(any("packet_hash" in error for error in errors))

    def test_hive_builder_emits_pantograph_consumable_draft_binding(self) -> None:
        draft_path = self.root / "lean" / "Draft.lean"
        draft_path.write_text("namespace Demo\ntheorem next : True := by trivial\nend Demo\n", encoding="utf-8")
        receipt = {
            "schema": "info_geometry.opengauss.contract_bound_draft.v1",
            "contract": self.contract,
            "contract_sha256": canonical_digest(self.contract),
            "source_path": "lean/Draft.lean",
            "source_sha256": hashlib.sha256(draft_path.read_bytes()).hexdigest(),
            "target_name": "Demo.next",
            "declaration_signature": "theorem next : True",
            "target_expression": "True",
        }
        receipt_path = self.root / "artifacts" / "draft.json"
        receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
        contract_path = self.root / "artifacts" / "contract.json"
        contract_path.write_text(json.dumps(self.contract), encoding="utf-8")
        args = SimpleNamespace(
            symbolic_origin_ref=[], invariant_ref=["invariant:demo"],
            repo_anchor_ref=["lean/Owner.lean"], candidate_dependency=["Demo.base"],
            ground_truth_contract=str(contract_path), draft_receipt=str(receipt_path),
            packet_hash="", formal_target_kind="theorem", formal_target_summary="Demo.next",
            formal_target_shape="", bridge_claim="A source-bound candidate.",
            novelty_summary="No novelty claim.", duplication_assessment="",
            pressure_point=[], lineage_id="lineage-demo", origin_run_id="run-demo",
            revision=1, created_by_agent="test", agent_role="test", backend="test",
            task_id="", session_key="", created_at="2026-01-01T00:00:00Z",
            updated_at="2026-01-01T00:00:00Z", tag=[], notes="", parent_ref=[],
            evidence_ref=[], source_hash=[], id="", status="legalized", packet_version="1.0.0",
            admissibility_state="admissible_for_probe", cost_class="low",
            anchor_completeness="", target_namespace_candidate=[], target_module_candidate=[],
            representation_class="translator", representation_depth=["source"],
        )
        with patch("tools.infra.hive_packet_build.ROOT", self.root), patch(
            "tools.infra.hive_packet_validate.ROOT", self.root
        ):
            packet = build_theorem_candidate(args)
            self.assertEqual(validate_ground_truth_candidate_integrity(packet), [])
            self.assertEqual(CandidatePacket.from_dict(packet).formal_target, "True")

    def test_contract_bound_draft_writes_valid_source_receipt(self) -> None:
        contract_path = self.root / "artifacts" / "contract.json"
        contract_path.write_text(json.dumps(self.contract), encoding="utf-8")
        output = self.root / "lean" / "DemoDraft.lean"
        with patch("tools.infra.opengauss_cli._REPO_ROOT", self.root), patch(
            "tools.infra.opengauss_cli.execute_checkpoint"
        ):
            self.assertEqual(opengauss_main([
                "draft", "--headline", "next", "--signature", ": True",
                "--namespace", "Demo", "--ground-truth-contract", str(contract_path),
                "--output", str(output),
            ]), 0)
        receipt_path = output.with_name(output.name + ".opengauss.json")
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        checked = validate_draft_receipt_payload(receipt, repo_root=self.root)
        self.assertEqual(checked["target_expression"], "True")


if __name__ == "__main__":
    unittest.main()

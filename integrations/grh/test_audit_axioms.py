"""Failure-boundary regressions for the GRH proof-evidence parser.

These tests use synthetic reports only. They do not constitute a Lean audit.
Run with `python3 -m unittest discover -s integrations/grh -p 'test_audit_axioms.py'`.
"""

from __future__ import annotations

import copy
import json
import unittest

from audit_axioms import ALLOWED_AXIOMS, AuditFailure, NATIVE_OWNERS, OWNERS, validate_output


def evidence(scope: str = "integration") -> list[dict]:
    owners = NATIVE_OWNERS if scope == "native" else OWNERS
    declarations = [
        {"record": "grh_axiom_audit_declaration", "module": owner,
         "name": f"{owner}.exampleTheorem", "kind": "theorem", "unsafe": False,
         "partial": False, "axioms": sorted(ALLOWED_AXIOMS)}
        for owner in owners
    ]
    return declarations + [
        {"record": "grh_axiom_audit_summary", "status": "PASS", "scope": scope,
         "modules": list(owners),
         "declarations": len(declarations), "theorems": len(declarations),
         "axiom_whitelist": sorted(ALLOWED_AXIOMS)}
    ]


def render(records: list[dict]) -> str:
    return "\n".join(json.dumps(record) for record in records)


class AxiomEvidenceTests(unittest.TestCase):
    def test_complete_standard_report(self) -> None:
        result = validate_output(render(evidence()), lean_exit_code=0)
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(set(result["owner_counts"]), set(OWNERS))

    def test_native_scope_and_cross_scope_rejection(self) -> None:
        result = validate_output(render(evidence("native")), lean_exit_code=0, scope="native")
        self.assertEqual(set(result["owner_counts"]), set(NATIVE_OWNERS))
        with self.assertRaises(AuditFailure):
            validate_output(render(evidence("native")), lean_exit_code=0)
        with self.assertRaises(AuditFailure):
            validate_output(render(evidence()), lean_exit_code=0, scope="native")

    def test_rejects_proof_hole_custom_and_native_reduction_axioms(self) -> None:
        for axiom in ("sorryAx", "MyUnprovedGRH", "Lean.ofReduceBool"):
            with self.subTest(axiom=axiom):
                records = evidence()
                records[0]["axioms"].append(axiom)
                with self.assertRaises(AuditFailure):
                    validate_output(render(records), lean_exit_code=0)

    def test_rejects_nonzero_lean_exit_even_with_complete_summary(self) -> None:
        with self.assertRaises(AuditFailure):
            validate_output(render(evidence()), lean_exit_code=1)

    def test_print_axioms_alone_is_not_evidence(self) -> None:
        with self.assertRaises(AuditFailure):
            validate_output("theorem uses axioms [propext, Classical.choice, Quot.sound]",
                            lean_exit_code=0)

    def test_rejects_missing_owner_even_if_totals_are_adjusted(self) -> None:
        records = evidence()[1:]
        records[-1]["declarations"] -= 1
        records[-1]["theorems"] -= 1
        with self.assertRaises(AuditFailure):
            validate_output(render(records), lean_exit_code=0)

    def test_rejects_duplicate_declaration_even_if_totals_are_adjusted(self) -> None:
        records = evidence()
        records.insert(0, copy.deepcopy(records[0]))
        records[-1]["declarations"] += 1
        records[-1]["theorems"] += 1
        with self.assertRaises(AuditFailure):
            validate_output(render(records), lean_exit_code=0)

    def test_rejects_expanded_allowlist(self) -> None:
        records = evidence()
        records[-1]["axiom_whitelist"].append("sorryAx")
        records[0]["axioms"].append("sorryAx")
        with self.assertRaises(AuditFailure):
            validate_output(render(records), lean_exit_code=0)

    def test_rejects_partial_unsafe_and_introduced_axiom(self) -> None:
        for field, value in (("partial", True), ("unsafe", True), ("kind", "axiom")):
            with self.subTest(field=field):
                records = evidence()
                records[0][field] = value
                with self.assertRaises(AuditFailure):
                    validate_output(render(records), lean_exit_code=0)

    def test_rejects_truncated_and_duplicate_summaries(self) -> None:
        for records in (evidence()[:-1], evidence() + [evidence()[-1]]):
            with self.subTest(records=len(records)):
                with self.assertRaises(AuditFailure):
                    validate_output(render(records), lean_exit_code=0)


if __name__ == "__main__":
    unittest.main()

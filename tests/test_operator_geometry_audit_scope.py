"""An unrelated PASS or an incomplete native enumeration must fail closed."""
import copy
import json
import unittest

from tools.quality.check_operator_geometry import validate_audit_output


class AuditScopeTests(unittest.TestCase):
    def setUp(self):
        self.owners = ["InfoGeometry.Test.First", "InfoGeometry.Test.Second"]
        self.records = [
            {"record": "declaration", "name": "first", "module": self.owners[0],
             "kind": "theorem", "unsafe": False, "partial": False,
             "axioms": ["propext"], "dependencies": ["propext"], "owned_dependencies": []},
            {"record": "declaration", "name": "second", "module": self.owners[1],
             "kind": "theorem", "unsafe": False, "partial": False,
             "axioms": ["propext"], "dependencies": ["first"], "owned_dependencies": ["first"]},
            {"record": "summary", "status": "PASS", "modules": self.owners,
             "declarations": 2, "empty_modules": [],
             "axiom_whitelist": ["propext", "Classical.choice", "Quot.sound"]},
        ]

    def encoded(self, records):
        return "\n".join(json.dumps(record) for record in records)

    def test_exact_scope(self):
        self.assertEqual(validate_audit_output(self.encoded(self.records), self.owners)["status"], "PASS")

    def test_wrong_passing_scope(self):
        with self.assertRaises(RuntimeError):
            validate_audit_output(self.encoded(self.records), ["InfoGeometry.Unrelated"])

    def test_incomplete_or_duplicate_enumeration(self):
        for records in (self.records[1:], [self.records[0], self.records[0], self.records[-1]]):
            with self.subTest(records=records), self.assertRaises(RuntimeError):
                validate_audit_output(self.encoded(records), self.owners)

    def test_unexpected_or_missing_module(self):
        records = copy.deepcopy(self.records)
        records[1]["module"] = "InfoGeometry.Unrelated"
        with self.assertRaises(RuntimeError):
            validate_audit_output(self.encoded(records), self.owners)

    def test_empty_owner_requires_explicit_permission(self):
        records = [self.records[0], copy.deepcopy(self.records[-1])]
        records[-1].update(declarations=1, empty_modules=[self.owners[1]])
        encoded = self.encoded(records)
        with self.assertRaises(RuntimeError):
            validate_audit_output(encoded, self.owners)
        validate_audit_output(encoded, self.owners, (self.owners[1],))

    def test_extra_or_missing_summary(self):
        for records in (self.records[:-1], self.records + [self.records[-1]],
                        self.records + [{"record": "unrecognized"}]):
            with self.subTest(records=records), self.assertRaises(RuntimeError):
                validate_audit_output(self.encoded(records), self.owners)

    def test_unsafe_partial_axiom_and_wrong_whitelist(self):
        for field, value in (("unsafe", True), ("partial", True),
                             ("kind", "axiom"), ("axioms", ["sorryAx"])):
            records = copy.deepcopy(self.records)
            records[0][field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                validate_audit_output(self.encoded(records), self.owners)
        records = copy.deepcopy(self.records)
        records[-1]["axiom_whitelist"].append("sorryAx")
        with self.assertRaises(RuntimeError):
            validate_audit_output(self.encoded(records), self.owners)

    def test_unresolved_owned_dependency(self):
        records = copy.deepcopy(self.records)
        records[1]["owned_dependencies"] = ["unreported"]
        with self.assertRaises(RuntimeError):
            validate_audit_output(self.encoded(records), self.owners)

    def test_missing_or_unknown_declaration_kind(self):
        for kind in (None, "unrecognized"):
            records = copy.deepcopy(self.records)
            if kind is None:
                del records[0]["kind"]
            else:
                records[0]["kind"] = kind
            with self.subTest(kind=kind), self.assertRaises(RuntimeError):
                validate_audit_output(self.encoded(records), self.owners)

    def test_omitted_owned_dependency_edge(self):
        records = copy.deepcopy(self.records)
        records[1]["owned_dependencies"] = []
        with self.assertRaises(RuntimeError):
            validate_audit_output(self.encoded(records), self.owners)


if __name__ == "__main__":
    unittest.main()

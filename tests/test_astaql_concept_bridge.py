import argparse
import unittest

from tools.infra.astaql_concept_bridge import _pattern, _positive, build_query


class AstaqlConceptBridgeTests(unittest.TestCase):
    def test_pattern_escapes_terms_and_joins_alternatives(self):
        self.assertEqual(_pattern(("Tomita", "KMS+")), r"tomita|kms\+")

    def test_pattern_rejects_empty_terms(self):
        with self.assertRaises(ValueError):
            _pattern(("", "  "))

    def test_positive_bound_rejects_zero_and_non_integer(self):
        with self.assertRaises(argparse.ArgumentTypeError):
            _positive("0", "--depth")
        with self.assertRaises(argparse.ArgumentTypeError):
            _positive("deep", "--depth")

    def test_query_uses_only_compiler_dependency_edges_and_reports_paths(self):
        query = build_query()
        self.assertIn('PRUNE e.kind NOT IN ["type", "value"]', query)
        self.assertIn('FILTER e.kind IN ["type", "value"]', query)
        self.assertIn("quantumPath: qpath.path", query)
        self.assertIn("classicalPath: cpath.path", query)
        self.assertIn("quantumToClassicalPaths", query)
        self.assertIn("classicalToQuantumPaths", query)
        self.assertIn("typeShapeHash", query)
        self.assertIn("valueShapeHash", query)
        self.assertIn("quantumMatchedCount", query)
        self.assertIn("classicalMatchedCount", query)
        self.assertIn("@quantum_names", query)
        self.assertIn("@classical_names", query)
        self.assertIn("d.name IN @quantum_names", query)
        self.assertIn("d.name IN @classical_names", query)

    def test_query_supports_module_scopes(self):
        query = build_query()
        self.assertIn("@quantum_module_prefix", query)
        self.assertIn("@classical_module_prefix", query)


if __name__ == "__main__":
    unittest.main()

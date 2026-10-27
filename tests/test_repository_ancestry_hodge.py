"""Small exact mathematical fixtures for ancestry_hodge; no Lean/repo tests."""

from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest

try:
    import numpy as np
    from scipy import sparse
except ModuleNotFoundError as exc:
    if exc.name not in {"numpy", "scipy"}:
        raise
    raise unittest.SkipTest(
        "Install tools/repository_evolution/requirements-hodge.txt for Hodge tests"
    ) from exc

from tools.repository_evolution.ancestry_hodge import analyze_export, causal_cone, graph_from_export, main


def export(*rows):
    return {"schema": "fixture/v1", "commits": [{"sha": sha, "parents": list(parents)} for sha, parents in rows]}


class AncestryHodgeTests(unittest.TestCase):
    def assert_checks(self, analysis):
        self.assertTrue(analysis.report["all_exact_checks_passed"])
        self.assertTrue(all(analysis.report["checks"].values()))
        self.assertEqual(analysis.B.dtype, np.dtype(np.int64))

    def test_actual_incidence_orientation_and_root_energy(self):
        a = analyze_export(export(("A", ()), ("B", ("A",))))
        np.testing.assert_array_equal(a.B.toarray(), [[-1], [1]])
        np.testing.assert_array_equal(a.D.toarray(), [[0, 0, -1], [0, 0, 1], [-1, 1, 0]])
        np.testing.assert_array_equal(a.Gamma.diagonal(), [1, 1, -1])
        self.assertEqual(a.report["selected_root"]["root_delta_D_norm_sq"], 1)
        self.assertFalse(a.report["selected_root"]["vertex_delta_is_harmonic"])
        self.assert_checks(a)

    def test_dag_diamond_has_one_undirected_cycle(self):
        data = export(("A", ()), ("B", ("A",)), ("C", ("A",)), ("D", ("B", "C")))
        a = analyze_export(data)
        self.assertTrue(a.report["graph_structure"]["directed_acyclic"])
        self.assertEqual(a.report["metrics"]["betti1"], 1)
        self.assertEqual(a.report["metrics"]["dirac_kernel_dimension"], 2)
        self.assertEqual(a.report["metrics"]["chiral_index_even_to_odd"], 0)
        self.assertEqual(a.forest.edge_indices, [0, 1, 2])
        np.testing.assert_array_equal(a.Z.toarray(), [[-1], [1], [-1], [1]])
        np.testing.assert_array_equal((a.B @ a.Z).toarray(), np.zeros((4, 1), dtype=int))
        self.assertEqual(causal_cone(data, "D", "past"), {"A", "B", "C"})
        self.assertEqual(causal_cone(data, "A", "future"), {"B", "C", "D"})
        self.assertEqual(causal_cone(data, "B", "future"), {"D"})
        cycle = a.report["representative_cycle"]
        self.assertEqual(cycle["vertices"][0], cycle["vertices"][-1])
        self.assert_checks(a)

    def test_directed_cycle_does_not_break_chirality(self):
        data = export(("A", ("C",)), ("B", ("A",)), ("C", ("B",)))
        a = analyze_export(data)
        self.assertFalse(a.report["graph_structure"]["directed_acyclic"])
        self.assertEqual(a.report["metrics"]["betti1"], 1)
        self.assertEqual(a.report["roots"], [])
        self.assertIsNone(a.report["selected_root"])
        self.assertTrue(a.report["checks"]["Gamma_D_plus_D_Gamma_is_zero"])
        self.assertTrue(a.report["metrics"]["commutator_is_nonzero"])
        self.assertEqual(causal_cone(data, "A", "future"), {"B", "C"})
        self.assert_checks(a)

    def test_disconnected_graph_includes_isolated_zero_mode(self):
        a = analyze_export(export(("A", ()), ("B", ("A",)), ("C", ())))
        metrics = a.report["metrics"]
        self.assertEqual((metrics["components"], metrics["betti0"], metrics["betti1"]), (2, 2, 0))
        self.assertEqual(metrics["dirac_kernel_dimension"], 2)
        self.assertEqual(metrics["chiral_index_even_to_odd"], 2)
        isolated = next(root for root in a.report["roots"] if root["sha"] == "C")
        self.assertEqual(isolated["root_delta_D_norm_sq"], 0)
        self.assertTrue(isolated["vertex_delta_is_harmonic"])
        self.assert_checks(a)

    def test_missing_parents_are_explicit_boundary_vertices(self):
        a = analyze_export(export(("child", ("outside",))))
        self.assertEqual(a.graph.vertices, ["child", "outside"])
        np.testing.assert_array_equal(a.B.toarray(), [[1], [-1]])
        self.assertEqual(a.report["metrics"]["vertices"], 2)
        self.assertEqual(a.report["metrics"]["record_count"], 1)
        self.assertEqual(a.report["metrics"]["boundary_vertex_count"], 1)
        self.assertEqual(a.report["graph_structure"]["synthesized_boundary_vertices"], ["outside"])
        self.assertTrue(a.report["selected_root"]["boundary"])
        self.assert_checks(a)

    def test_additional_parent_can_join_first_parent_components(self):
        a = analyze_export(export(("A", ()), ("B", ()), ("C", ("A", "B"))))
        self.assertEqual(a.forest.edge_indices, [0, 1])
        self.assertEqual(a.report["metrics"]["components"], 1)
        self.assertEqual(a.report["metrics"]["betti1"], 0)
        self.assert_checks(a)

    def test_parallel_edges_have_independent_cycle_pivot(self):
        a = analyze_export(export(("A", ()), ("B", ("A", "A"))))
        self.assertEqual(a.report["metrics"]["betti1"], 1)
        np.testing.assert_array_equal(a.Z.toarray(), [[-1], [1]])
        self.assert_checks(a)

    def test_self_loop_boundary_cancels_but_keeps_edge_zero_mode(self):
        a = analyze_export(export(("A", ("A",))))
        self.assertEqual(a.B.nnz, 0)
        self.assertEqual(a.D.shape, (2, 2))
        self.assertEqual(a.D.nnz, 0)
        self.assertEqual(a.report["metrics"]["betti1"], 1)
        self.assertEqual(a.report["metrics"]["dirac_kernel_dimension"], 2)
        self.assertFalse(a.report["metrics"]["commutator_is_nonzero"])
        np.testing.assert_array_equal(a.Z.toarray(), [[1]])
        self.assert_checks(a)

    def test_empty_and_edgeless_carriers(self):
        for data, n in ((export(), 0), (export(("A", ()), ("B", ())), 2)):
            with self.subTest(vertices=n):
                a = analyze_export(data)
                self.assertEqual(a.D.shape, (n, n))
                self.assertEqual(a.report["metrics"]["dirac_kernel_dimension"], n)
                self.assertIsNone(a.report["representative_cycle"])
                self.assert_checks(a)

    def test_rejects_display_only_or_duplicate_records(self):
        with self.assertRaises(ValueError):
            graph_from_export({"nodes": [{"sha": "A"}], "links": []})
        with self.assertRaises(ValueError):
            graph_from_export(export(("A", ()), ("A", ())))

    def test_cli_witness_reconstructs_exact_cycle_basis(self):
        data = export(("A", ()), ("B", ("A",)), ("C", ("A",)), ("D", ("B", "C")))
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "input.json"
            report_path = Path(folder) / "report.json"
            witness_path = Path(folder) / "cycles.json"
            raw = json.dumps(data, indent=2).encode()
            source.write_bytes(raw)
            with redirect_stdout(io.StringIO()):
                result = main(["--input", str(source), "--out", str(report_path), "--witness-out", str(witness_path)])
            self.assertEqual(result, 0)
            report = json.loads(report_path.read_text())
            witness = json.loads(witness_path.read_text())
            self.assertEqual(report["source"]["sha256"], hashlib.sha256(raw).hexdigest())
            self.assertEqual(report["witness"]["sha256"], hashlib.sha256(witness_path.read_bytes()).hexdigest())
            self.assertEqual(witness["source_sha256"], report["source"]["sha256"])
            n, m, k = len(witness["vertices"]), len(witness["edges"]), len(witness["cycles"])
            b = sparse.lil_matrix((n, m), dtype=np.int64)
            z = sparse.lil_matrix((m, k), dtype=np.int64)
            for j, (u, v, _) in enumerate(witness["edges"]):
                b[u, j] -= 1
                b[v, j] += 1
            for j, cycle in enumerate(witness["cycles"]):
                for edge_index, sign in cycle["signed_edges"]:
                    z[edge_index, j] = sign
            product = (b.tocsr() @ z.tocsr()).tocsr()
            product.eliminate_zeros()
            self.assertEqual(product.nnz, 0)
            self.assertEqual(k, 1)
            self.assertTrue(report["all_exact_checks_passed"])


if __name__ == "__main__":
    unittest.main()

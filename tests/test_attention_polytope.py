"""Exact arithmetic tests; these do not replace Lean kernel checking."""
import itertools
import io
import json
import unittest
from unittest.mock import patch
from fractions import Fraction as F
from tools.attention_polytope import (
    RoutingTerm, decompose, normalize_rows, rational_matrix, readout,
    reconstruct, route_readout, verify_certificate, expected_causal_core_rank, main,
)


def simplex_grid(columns, denominator):
    return [tuple(F(x, denominator) for x in row)
            for row in itertools.product(range(denominator + 1), repeat=columns)
            if sum(row) == denominator]


class AttentionPolytopeTests(unittest.TestCase):
    def check_matrix(self, matrix):
        terms = decompose(matrix)
        self.assertTrue(verify_certificate(matrix, terms))
        self.assertEqual(reconstruct(terms, len(matrix), len(matrix[0])),
                         rational_matrix(matrix))
        bound = sum(x > 0 for row in rational_matrix(matrix) for x in row) - len(matrix) + 1
        self.assertLessEqual(len(terms), bound)
        values = [[j - 2, F(1, j + 1), (-1) ** j] for j in range(len(matrix[0]))]
        self.assertEqual(readout(matrix, values), route_readout(terms, values))

    def test_exhaustive_two_by_three_quarters(self):
        for rows in itertools.product(simplex_grid(3, 4), repeat=2):
            with self.subTest(rows=rows):
                self.check_matrix(rows)

    def test_exhaustive_three_by_three_thirds(self):
        for rows in itertools.product(simplex_grid(3, 3), repeat=3):
            with self.subTest(rows=rows):
                self.check_matrix(rows)

    def test_causal_mask(self):
        for n in range(1, 10):
            matrix = [[F(1, i + 1) if j <= i else F(0) for j in range(n)]
                      for i in range(n)]
            self.check_matrix(matrix)
            for term in decompose(matrix):
                self.assertTrue(all(j <= i for i, j in enumerate(term.route)))

    def test_causal_core_rank_matches_sparse_route_coupling(self):
        for n in range(1, 5):
            row_grids = [simplex_grid(i + 1, 3) for i in range(n)]
            for rows in itertools.product(*row_grids):
                matrix = [tuple(row) + (F(0),) * (n - len(row)) for row in rows]
                expected = sum((t.weight * sum(j == i for i, j in enumerate(t.route))
                                for t in decompose(matrix)), F(0))
                self.assertEqual(expected_causal_core_rank(matrix), expected)

    def test_causal_core_only_does_not_enumerate_routes(self):
        with patch("sys.argv", ["attention_polytope", "input.json", "--causal-core-only"]), \
                patch("pathlib.Path.read_text", return_value='{"attention": [[1, 0], ["1/3", "2/3"]]}'), \
                patch("tools.attention_polytope.decompose", side_effect=AssertionError("must not run")), \
                patch("sys.stdout", new_callable=io.StringIO) as output:
            main()
        result = json.loads(output.getvalue())
        self.assertEqual(result["expected_causal_core_rank"], "5/3")
        self.assertEqual(result["expected_causal_core_fraction"], "5/6")
        self.assertFalse(result["route_decomposition_performed"])

    def test_causal_core_rejects_wrong_carrier_or_mask(self):
        for matrix in ([[1, 0, 0], [0, 1, 0]], [[0, 1], [1, 0]], [[2, 0], [0, 1]], []):
            with self.subTest(matrix=matrix), self.assertRaises(ValueError):
                expected_causal_core_rank(matrix)

    def test_general_mask(self):
        matrix = [[F(1, 2), 0, F(1, 2)], [0, 1, 0], [F(1, 3), 0, F(2, 3)]]
        self.check_matrix(matrix)
        for term in decompose(matrix):
            self.assertTrue(all(matrix[i][j] > 0 for i, j in enumerate(term.route)))

    def test_many_to_one_routes_are_required(self):
        self.assertEqual(decompose([[1, 0], [1, 0]]),
                         (RoutingTerm(F(1), (0, 0)),))

    def test_concrete_example(self):
        matrix = [[F(1, 2), F(1, 2), 0], [0, F(1, 3), F(2, 3)],
                  [F(1, 4), 0, F(3, 4)]]
        self.assertEqual(decompose(matrix), (
            RoutingTerm(F(1, 4), (0, 1, 0)),
            RoutingTerm(F(1, 12), (0, 1, 2)),
            RoutingTerm(F(1, 6), (0, 2, 2)),
            RoutingTerm(F(1, 2), (1, 2, 2)),
        ))
        self.check_matrix(matrix)

    def test_does_not_mutate_input(self):
        matrix = [[F(1, 2), F(1, 2)], [F(1, 4), F(3, 4)]]
        original = [row[:] for row in matrix]
        decompose(matrix)
        self.assertEqual(matrix, original)

    def test_no_silent_normalization(self):
        with self.assertRaises(ValueError):
            decompose([[2, 1]])
        self.check_matrix(normalize_rows([[2, 1]]))

    def test_invalid_inputs(self):
        for matrix in ([], [[]], [[1], [1, 0]], [[2, -1]], [[0, 0]], [[float('nan')]]):
            with self.subTest(matrix=matrix), self.assertRaises(ValueError):
                decompose(matrix)

    def test_bad_certificates(self):
        self.assertFalse(verify_certificate([[1, 0]], []))
        self.assertFalse(verify_certificate([[1, 0]], [RoutingTerm(F(1), (1,))]))
        self.assertFalse(verify_certificate([[1, 0]], [RoutingTerm(F(1), (2,))]))
        self.assertFalse(verify_certificate([[1, 0]], [RoutingTerm(F(1, 2), (0,))]))

    def test_nonunique_mixture_coordinates(self):
        matrix = [[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]]
        correlated = [RoutingTerm(F(1, 2), (0, 0)), RoutingTerm(F(1, 2), (1, 1))]
        anticorrelated = [RoutingTerm(F(1, 2), (0, 1)), RoutingTerm(F(1, 2), (1, 0))]
        self.assertTrue(verify_certificate(matrix, correlated))
        self.assertTrue(verify_certificate(matrix, anticorrelated))
        self.assertNotEqual(correlated, anticorrelated)


if __name__ == '__main__':
    unittest.main()

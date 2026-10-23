"""Exact-rational compression regression tests; not a Lean proof of Python."""
import argparse
import io
import itertools
import json
from fractions import Fraction as F
from pathlib import Path
import unittest
from unittest.mock import patch

from tools import attention_polytope as owner


def simplex_grid(columns, denominator):
    for row in itertools.product(range(denominator + 1), repeat=columns):
        if sum(row) == denominator:
            yield tuple(F(x, denominator) for x in row)


def determinant(matrix):
    """Independent small Gram-determinant oracle, not the candidate's RREF."""
    result = F(0)
    for perm in itertools.permutations(range(len(matrix))):
        inversions = sum(perm[i] > perm[j] for i in range(len(perm))
                         for j in range(i + 1, len(perm)))
        term = F((-1) ** inversions)
        for i, j in enumerate(perm):
            term *= matrix[i][j]
        result += term
    return result


class ReadoutCompressionTests(unittest.TestCase):
    def check_compression(self, matrix, values):
        original = owner.rational_matrix(matrix)
        table = owner.rational_matrix(values)
        compressed = owner.compress_readout(matrix, values)
        self.assertIsInstance(compressed, tuple)
        self.assertEqual(len(compressed), len(original))
        self.assertEqual(owner.readout(compressed, table), owner.readout(original, table))
        for source, row in zip(original, compressed):
            self.assertIsInstance(row, tuple)
            self.assertEqual(len(row), len(source))
            self.assertTrue(all(isinstance(x, F) and x >= 0 for x in row))
            self.assertEqual(sum(row), 1)
            active = [j for j, x in enumerate(row) if x > 0]
            self.assertTrue(all(source[j] > 0 for j in active))
            self.assertLessEqual(len(active), len(table[0]) + 1)
            cols = [(F(1),) + table[j] for j in active]
            gram = [[sum(x * y for x, y in zip(a, b)) for b in cols] for a in cols]
            self.assertNotEqual(determinant(gram), 0)
        self.assertEqual(owner.compress_readout(compressed, table), compressed)
        self.assertEqual(owner.compress_readout(matrix, values), compressed)
        return compressed

    def test_exhaustive_rational_simplex_and_scalar_value_grids(self):
        # All 35 quarter-simplex rows and all 81 rational scalar value tables.
        rows = list(simplex_grid(4, 4))
        for coordinates in itertools.product((F(-2, 3), F(0), F(5, 7)), repeat=4):
            values = [[x] for x in coordinates]
            self.check_compression(rows, values)

    def test_exhaustive_two_row_grid_with_affine_dependencies(self):
        grid = list(simplex_grid(3, 4))
        values = [[F(-1, 3), F(7, 5)], [0, 2], [F(1, 3), F(13, 5)]]
        for matrix in itertools.product(grid, repeat=2):
            self.check_compression(matrix, values)

    def test_affinely_independent_support_is_unchanged(self):
        values = [[0, 0], [1, 0], [0, 1]]
        rows = list(simplex_grid(3, 5))
        self.assertEqual(self.check_compression(rows, values), tuple(rows))

    def test_duplicate_values_and_rank_zero(self):
        for width in (1, 2, 7, 31):
            values = [[F(2, 7), -3, 0, 9]] * width
            row = [F(1, width)] * width
            result = self.check_compression([row], values)
            self.assertEqual(sum(x > 0 for x in result[0]), 1)

    def test_degenerate_affine_line_in_high_dimension(self):
        values = [[F(j, 3), F(2 * j + 1, 3), 7, -j, F(j - 2, 9)] for j in range(19)]
        result = self.check_compression([[F(1, 19)] * 19], values)
        self.assertLessEqual(sum(x > 0 for x in result[0]), 2)

    def test_causal_and_irregular_masks(self):
        for n in range(1, 13):
            values = [[F(j, 7), F(j * j, 11)] for j in range(n)]
            causal = [[F(1, i + 1) if j <= i else F(0) for j in range(n)] for i in range(n)]
            self.check_compression(causal, values)
            masked = [[1 if (i + j) % 3 == 0 or j == i else 0 for j in range(n)]
                      for i in range(n)]
            self.check_compression(owner.normalize_rows(masked), values)

    def test_large_key_count_low_dimension(self):
        m = 257
        values = [[F(j - 128, 17), F((j * j) % 37, 19)] for j in range(m)]
        raw = [[(j % 11 + 1) if (j + i) % 5 else 0 for j in range(m)] for i in range(4)]
        result = self.check_compression(owner.normalize_rows(raw), values)
        self.assertTrue(all(sum(x > 0 for x in row) <= 3 for row in result))

    def test_inputs_are_not_mutated_and_no_implicit_normalization(self):
        matrix = [[F(1, 3)] * 3]
        values = [[0], [1], [2]]
        snapshot = ([row[:] for row in matrix], [row[:] for row in values])
        self.check_compression(matrix, values)
        self.assertEqual((matrix, values), snapshot)
        with self.assertRaises(ValueError):
            owner.compress_readout([[2, 1, 1]], values)

    def test_invalid_inputs(self):
        bad = [([], [[0]]), ([[]], [[0]]), ([[1], [1, 0]], [[0]]),
               ([[2, -1]], [[0], [1]]), ([[0, 0]], [[0], [1]]),
               ([[1]], []), ([[1]], [[]]), ([[1]], [[0], [1]]),
               ([[F(1, 2), F(1, 2)]], [[1], [1, 2]]),
               ([[float("nan")]], [[0]]), ([[1]], [[float("inf")]]),
               ([["1/0"]], [[0]]), ([[1]], [["not rational"]])]
        for matrix, values in bad:
            with self.subTest(matrix=matrix, values=values), self.assertRaises(ValueError):
                owner.compress_readout(matrix, values)

    def run_cli(self, payload, *flags):
        with patch.object(Path, "read_text", return_value=payload), \
                patch.object(owner, "decompose", side_effect=AssertionError("routes forbidden")), \
                patch.object(owner, "expected_causal_core_rank", side_effect=AssertionError("wrong mode")), \
                patch("sys.stdout", new_callable=io.StringIO) as output, \
                patch("sys.argv", ["attention_polytope", "input.json", "--compress-readout", *flags]):
            owner.main()
        return json.loads(output.getvalue())

    def test_cli_exact_decimals_no_routes_and_distinct_change_flags(self):
        report = self.run_cli('{"attention": [[0.2, 0.3, 0.5]], "values": [[4], [4], [4]]}')
        self.assertFalse(report["input_normalization_changed"])
        self.assertTrue(report["compression_changed"])
        self.assertTrue(report["input_changed"])
        self.assertTrue(report["support_contained_in_input"])
        self.assertFalse(report["route_decomposition_performed"])
        self.assertEqual(report["readout"], [["4"]])
        self.assertEqual(report["compressed_row_support_sizes"], [1])
        self.assertNotIn("terms", report)
        self.assertNotIn("number_of_routes", report)

    def test_cli_normalization_separate_from_compression(self):
        report = self.run_cli('{"attention": [[2, 2]], "values": [[0], [1]]}', "--normalize-rows")
        self.assertTrue(report["input_normalization_changed"])
        self.assertFalse(report["compression_changed"])
        self.assertTrue(report["input_changed"])
        self.assertEqual(report["compressed_attention"], [["1/2", "1/2"]])
        report = self.run_cli('{"attention": [[2, 2, 0]], "values": [[1], [1], [9]]}', "--normalize-rows")
        self.assertTrue(report["input_normalization_changed"])
        self.assertTrue(report["compression_changed"])
        self.assertEqual(report["compressed_attention"][0][2], "0")
        report = self.run_cli('{"attention": [["1/2", "1/2"]], "values": [[0], [1]]}',
                              "--normalize-rows")
        self.assertFalse(report["input_normalization_changed"])
        self.assertFalse(report["compression_changed"])
        self.assertFalse(report["input_changed"])

    def test_cli_requires_values_and_excludes_causal_only(self):
        with patch("sys.stderr", new_callable=io.StringIO):
            with self.assertRaises(SystemExit) as missing:
                self.run_cli('{"attention": [[1]]}')
            self.assertEqual(missing.exception.code, 2)
            with self.assertRaises(SystemExit) as conflict:
                self.run_cli('{"attention": [[1]], "values": [[0]]}', "--causal-core-only")
            self.assertEqual(conflict.exception.code, 2)

    def test_noncompression_mode_leaves_existing_dispatch_intact(self):
        args = argparse.Namespace(compress_readout=False)
        self.assertIsNone(owner.compression_cli_result(args, {}, (), ()))


if __name__ == "__main__":
    unittest.main()

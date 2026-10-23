from fractions import Fraction as F
import itertools
import unittest
from tools.certified_caratheodory import Pivot, PruningResult, inputs, prune, readout, verify_certificate


class PruningTests(unittest.TestCase):
    def check(self, values, weights):
        v, p = inputs(values, weights)
        result = prune(v, p)
        self.assertTrue(verify_certificate(v, p, result))
        self.assertEqual(readout(v, result.weights), readout(v, p))
        self.assertLessEqual(sum(x > 0 for x in result.weights), len(v[0]) + 1)
        return result

    def test_collinear(self):
        self.check([[0], [1], [2]], [F(1, 3)] * 3)

    def test_square(self):
        self.check([[0, 0], [1, 0], [0, 1], [1, 1]], [F(1, 4)] * 4)

    def test_identical_values_require_more_than_ambient_bound(self):
        result = self.check([[7], [7], [7], [7]], [F(1, 4)] * 4)
        self.assertEqual(len(result.pivots), 3)
        self.assertEqual(sum(x > 0 for x in result.weights), 1)

    def test_dependent_below_dimension_threshold(self):
        result = self.check([[1, 2, 3]] * 3, [F(1, 3)] * 3)
        self.assertEqual(len(result.pivots), 2)

    def test_mask_preserved(self):
        result = self.check([[0], [999], [1], [2]], [F(1, 3), 0, F(1, 3), F(1, 3)])
        self.assertEqual(result.weights[1], 0)

    def test_zero_dimension(self):
        result = self.check([[], [], []], [F(1, 3)] * 3)
        self.assertEqual(sum(x > 0 for x in result.weights), 1)

    def test_no_pivot_on_independent_support(self):
        result = self.check([[0, 0], [1, 0], [0, 1]], [F(1, 3)] * 3)
        self.assertEqual(result.pivots, ())

    def test_exhaustive_3_key_scalar_values_and_weights(self):
        weights = [tuple(F(x, 4) for x in w) for w in itertools.product(range(5), repeat=3)
                   if sum(w) == 4]
        for values in itertools.product(range(3), repeat=3):
            for p in weights:
                with self.subTest(values=values, p=p):
                    self.check([[x] for x in values], p)

    def test_forged_direction_rejected(self):
        v, p = inputs([[0], [1], [2]], [F(1, 3)] * 3)
        result = prune(v, p)
        forged = PruningResult(result.weights, (Pivot(0, F(1, 3), (F(1), F(-1), F(0))),))
        self.assertFalse(verify_certificate(v, p, forged))

    def test_forged_output_rejected(self):
        forged = PruningResult(weights=(F(1), F(0)), pivots=())
        self.assertFalse(verify_certificate([[0], [1]], [F(1, 2)] * 2, forged))

    def test_invalid_inputs(self):
        bad = [([], []), ([[0], [1, 2]], [F(1, 2)] * 2), ([[0], [1]], [2, -1]),
               ([[0], [1]], [1, 1]), ([[float('nan')]], [1])]
        for v, p in bad:
            with self.subTest(values=v), self.assertRaises(ValueError):
                prune(v, p)

    def test_input_unchanged(self):
        v = [[0], [1], [2]]
        p = [F(1, 3)] * 3
        self.check(v, p)
        self.assertEqual(v, [[0], [1], [2]])
        self.assertEqual(p, [F(1, 3)] * 3)

if __name__ == '__main__':
    unittest.main()

import importlib.util
import pathlib
import unittest

import numpy as np


MODULE_PATH = pathlib.Path(__file__).parents[1] / "python" / "bogoliubov_sinkhorn_experiment.py"
SPEC = importlib.util.spec_from_file_location("bogoliubov_sinkhorn_experiment", MODULE_PATH)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class SinkhornScalingTests(unittest.TestCase):
    def test_scales_positive_kernel_to_marginals(self):
        kernel = np.array([[1.0, 2.0], [3.0, 4.0]])
        marginal = np.ones(2)
        coupling, _, _ = MODULE.sinkhorn_scaling(kernel, marginal, marginal)

        np.testing.assert_allclose(coupling.sum(axis=1), marginal, atol=1e-8)
        np.testing.assert_allclose(coupling.sum(axis=0), marginal, atol=1e-8)
        self.assertTrue(np.all(coupling >= 0))

    def test_rejects_incompatible_marginal_mass(self):
        kernel = np.ones((2, 2))
        with self.assertRaises(ValueError):
            MODULE.sinkhorn_scaling(kernel, np.ones(2), np.array([1.0, 2.0]))

    def test_rejects_nonconvergence(self):
        kernel = np.array([[1.0, 2.0], [3.0, 4.0]])
        with self.assertRaises(RuntimeError):
            MODULE.sinkhorn_scaling(kernel, np.ones(2), np.ones(2), max_iter=1)

    def test_rejects_zero_kernel_entries(self):
        with self.assertRaises(ValueError):
            MODULE.sinkhorn_scaling(np.array([[1.0, 0.0], [1.0, 1.0]]),
                                    np.ones(2), np.ones(2))

    def test_rejects_nonfinite_inputs(self):
        kernel = np.array([[1.0, np.inf], [1.0, 1.0]])
        with self.assertRaises(ValueError):
            MODULE.sinkhorn_scaling(kernel, np.ones(2), np.ones(2))

    def test_experiment_requires_even_dimension(self):
        with self.assertRaises(ValueError):
            MODULE.run_experiment(dim=5)

    def test_experiment_requires_positive_epsilon(self):
        with self.assertRaises(ValueError):
            MODULE.run_experiment(epsilon=0)

    def test_experiment_requires_square_routing(self):
        with self.assertRaises(ValueError):
            MODULE.run_experiment(n_tokens=2, n_experts=3)


if __name__ == "__main__":
    unittest.main()

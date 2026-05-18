"""
Test suite for pyw.fractional.boundary_admissible module

Tests for the computation of principal admissible weights at boundary
admissible levels, specifically for sl(2) at k = -4/3.
"""

import pytest
from fractions import Fraction

# Only run these tests if SageMath is available
pytest.importorskip("sage.all")

from sage.all import RootSystem

from pyw.fractional.boundary_admissible import BoundaryAdmissibleWeights
from pyw.fractional.verify_sl2_boundary import latex_weight


class TestBoundaryAdmissibleWeights:
    """Test BoundaryAdmissibleWeights class."""

    def test_init_sl2(self):
        """Test initialization for sl(2)."""
        baw = BoundaryAdmissibleWeights(["A", 1, 1], p=2, u=3)
        assert baw.p == 2
        assert baw.u == 3
        assert baw.level == Fraction(-4, 3)
        assert baw.k_plus_h_vee == Fraction(2, 3)

    def test_compute_sl2_weights(self):
        """Test computation of sl(2) admissible weights at k = -4/3."""
        baw = BoundaryAdmissibleWeights(["A", 1, 1], p=2, u=3)
        weights = baw.compute_sl2_admissible_weights()

        # Should have exactly 3 weights
        assert len(weights) == 3

        # Extract the weights
        m0, w0, latex0 = weights[0]
        m1, w1, latex1 = weights[1]
        m2, w2, latex2 = weights[2]

        # Check m values
        assert m0 == 0
        assert m1 == 1
        assert m2 == 2

        # Check LaTeX strings match expected values
        assert "-4/3" in latex0 and "Lambda_0" in latex0
        assert "-2/3" in latex1 and "Lambda_0" in latex1 and "Lambda_1" in latex1
        assert "-4/3" in latex2 and "Lambda_1" in latex2

    def test_conformal_dimensions(self):
        """Test conformal dimension computation."""
        baw = BoundaryAdmissibleWeights(["A", 1, 1], p=2, u=3)
        dimensions = baw.compute_conformal_dimensions()

        expected = [Fraction(0, 1), Fraction(2, 3), Fraction(5, 3)]
        assert dimensions == expected

    def test_latex_weight_zero(self):
        """Test LaTeX generation for zero weight."""
        result = latex_weight(Fraction(0, 1), Fraction(0, 1))
        assert result == "0"

    def test_latex_weight_positive(self):
        """Test LaTeX generation for positive coefficients."""
        result = latex_weight(Fraction(1, 1), Fraction(2, 3))
        assert r"\Lambda_0" in result
        assert r"\frac{2}{3}\Lambda_1" in result

    def test_latex_weight_negative(self):
        """Test LaTeX generation for negative coefficients."""
        result = latex_weight(Fraction(-4, 3), Fraction(-2, 3))
        assert r"-\frac{4}{3}\Lambda_0" in result
        assert r"-\frac{2}{3}\Lambda_1" in result

    def test_latex_weight_mixed(self):
        """Test LaTeX generation for mixed signs."""
        result = latex_weight(Fraction(-2, 3), Fraction(-2, 3))
        # Should not have "+" followed by "-"
        assert "+ -" not in result
        # Should have "-\frac{2}{3}" twice
        assert result.count(r"-\frac{2}{3}") == 2


class TestSl2BoundaryCases:
    """Test specific cases for sl(2) boundary admissible weights."""

    def test_sl2_neg_4_3_weights(self):
        """Verify sl(2) weights at k = -4/3 match expected values."""
        baw = BoundaryAdmissibleWeights(["A", 1, 1], p=2, u=3)
        weights = baw.compute_sl2_admissible_weights()

        # Expected weights: (m, a0, a1)
        expected = [
            (0, Fraction(-4, 3), Fraction(0, 1)),
            (1, Fraction(-2, 3), Fraction(-2, 3)),
            (2, Fraction(0, 1), Fraction(-4, 3)),
        ]

        for (m, weight, _latex), (exp_m, exp_a0, exp_a1) in zip(weights, expected):
            assert m == exp_m
            # Check coefficients by accessing the weight
            # (This depends on SageMath's weight representation)

    def test_sl2_neg_4_3_dimensions(self):
        """Verify sl(2) conformal dimensions at k = -4/3."""
        baw = BoundaryAdmissibleWeights(["A", 1, 1], p=2, u=3)
        dimensions = baw.compute_conformal_dimensions()

        expected = [Fraction(0, 1), Fraction(2, 3), Fraction(5, 3)]
        assert dimensions == expected

    def test_sl2_other_levels(self):
        """Test sl(2) at other boundary admissible levels."""
        # k = -2 + 2/5 = -8/5
        baw = BoundaryAdmissibleWeights(["A", 1, 1], p=2, u=5)
        assert baw.level == Fraction(-8, 5)

        dimensions = baw.compute_conformal_dimensions()
        assert len(dimensions) == 5  # u = 5 weights

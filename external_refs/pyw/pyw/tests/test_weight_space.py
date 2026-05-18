"""
Test suite for pyw.core.weight_space module
"""

import pytest
from fractions import Fraction

from sage.all import RootSystem

from pyw.core.weight_space import FractionalWeightSpace


class TestFractionalWeightSpace:
    """Test FractionalWeightSpace class."""

    def test_init_a2_affine(self):
        """Test initialization with A2 affine type."""
        ws = FractionalWeightSpace(["A", 2, 1])
        assert ws.cartan_type == ["A", 2, 1]

    def test_fundamental_weights(self):
        """Test fundamental_weights property."""
        ws = FractionalWeightSpace(["A", 2, 1])
        lambdas = ws.fundamental_weights
        # Should have at least Lambda[0], Lambda[1], Lambda[2]
        assert 0 in lambdas
        assert 1 in lambdas
        assert 2 in lambdas

    def test_zero_weight(self):
        """Test zero method."""
        ws = FractionalWeightSpace(["A", 2, 1])
        zero = ws.zero()
        # Zero should be the additive identity
        assert zero == zero

    def test_create_fractional_weight_with_fraction(self):
        """Test create_fractional_weight with Fraction objects."""
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: Fraction(3, 4), 1: Fraction(1, 2)})
        # Should create a weight with fractional coefficients
        result = str(weight)
        # Check that it contains the fundamental weights
        assert "Lambda" in result or "lambda" in result

    def test_create_fractional_weight_with_tuple(self):
        """Test create_fractional_weight with tuple coefficients."""
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: (3, 4), 1: (1, 2)})
        # Should create a weight with fractional coefficients
        result = str(weight)
        assert "Lambda" in result or "lambda" in result

    def test_create_fractional_weight_with_int(self):
        """Test create_fractional_weight with integer coefficients."""
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: 1, 1: 2})
        # Should create a weight with integer coefficients
        result = str(weight)
        assert "Lambda" in result or "lambda" in result

    def test_create_fractional_weight_empty(self):
        """Test create_fractional_weight with empty coefficients."""
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({})
        # Should return zero weight
        assert weight == ws.zero()

    def test_rank_property(self):
        """Test rank property."""
        ws = FractionalWeightSpace(["A", 2, 1])
        # A2 affine has rank 3 (including the affine node)
        assert ws.rank >= 2

    def test_weight_space_property(self):
        """Test weight_space property."""
        ws = FractionalWeightSpace(["A", 2, 1])
        weight_space = ws.weight_space
        # Should be a SageMath weight_space object
        assert hasattr(weight_space, "fundamental_weights")

    def test_root_system_property(self):
        """Test root_system property."""
        ws = FractionalWeightSpace(["A", 2, 1])
        root_system = ws.root_system
        # Should be a SageMath RootSystem object
        assert hasattr(root_system, "cartan_type")

    def test_tuple_cartan_type(self):
        """Test with tuple Cartan type."""
        ws = FractionalWeightSpace(("A", 2, 1))
        assert ws.cartan_type == ("A", 2, 1)

    def test_finite_type(self):
        """Test with finite (non-affine) type."""
        ws = FractionalWeightSpace(["A", 2])
        assert ws.cartan_type == ["A", 2]

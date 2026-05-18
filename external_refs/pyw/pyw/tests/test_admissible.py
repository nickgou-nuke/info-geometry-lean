"""
Test suite for pyw.fractional.admissible module
"""

import pytest
from fractions import Fraction

from sage.all import RootSystem

from pyw.fractional.level import FractionalLevel
from pyw.fractional.admissible import AdmissibleWeight
from pyw.core.weight_space import FractionalWeightSpace


class TestAdmissibleWeight:
    """Test AdmissibleWeight class."""

    def test_init_with_fractional_level(self):
        """Test initialization with FractionalLevel."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: 1, 1: 1, 2: 1})

        aw = AdmissibleWeight(["A", 2, 1], weight, level)
        assert aw.cartan_type == ["A", 2, 1]
        assert aw.level == level

    def test_init_with_numeric_level(self):
        """Test initialization with numeric level."""
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: 1, 1: 1, 2: 1})

        aw = AdmissibleWeight(["A", 2, 1], weight, -5 / 3)
        assert aw.level == -5 / 3

    def test_setup_creates_weight_space(self):
        """Test _setup creates weight space."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: 1, 1: 1, 2: 1})

        aw = AdmissibleWeight(["A", 2, 1], weight, level)
        assert aw.weight_space is not None
        assert aw.root_system is not None

    def test_compute_affine_weyl_vector(self):
        """Test _compute_affine_weyl_vector."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: 1, 1: 1, 2: 1})

        aw = AdmissibleWeight(["A", 2, 1], weight, level)
        assert aw.rho_hat is not None

    def test_is_admissible_returns_bool(self):
        """Test is_admissible returns boolean."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: 1, 1: 1, 2: 1})

        aw = AdmissibleWeight(["A", 2, 1], weight, level)
        result = aw.is_admissible()
        assert isinstance(result, bool)

    def test_condition_1a_returns_bool(self):
        """Test _check_condition_1a returns boolean."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: 1, 1: 1, 2: 1})

        aw = AdmissibleWeight(["A", 2, 1], weight, level)
        result = aw._check_condition_1a()
        assert isinstance(result, bool)

    def test_condition_1b_returns_bool(self):
        """Test _check_condition_1b returns boolean."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        ws = FractionalWeightSpace(["A", 2, 1])
        weight = ws.create_fractional_weight({0: 1, 1: 1, 2: 1})

        aw = AdmissibleWeight(["A", 2, 1], weight, level)
        result = aw._check_condition_1b()
        assert isinstance(result, bool)

    def test_simple_admissible_weight(self):
        """Test with a simple admissible weight."""
        # For A2 affine with level k = -5/3, some weights are admissible
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        ws = FractionalWeightSpace(["A", 2, 1])

        # Try a dominant weight
        weight = ws.create_fractional_weight({0: 2, 1: 1, 2: 0})

        aw = AdmissibleWeight(["A", 2, 1], weight, level)
        # The result depends on the weight; just check it runs
        result = aw.is_admissible()
        assert isinstance(result, bool)

    def test_finite_type(self):
        """Test with finite (non-affine) type."""
        ws = FractionalWeightSpace(["A", 2])
        weight = ws.create_fractional_weight({0: 1, 1: 0})

        aw = AdmissibleWeight(["A", 2], weight, 1)
        assert aw.cartan_type == ["A", 2]

    def test_tuple_cartan_type(self):
        """Test with tuple Cartan type."""
        level = FractionalLevel(("A", 2, 1), p=4, u=3)
        ws = FractionalWeightSpace(("A", 2, 1))
        weight = ws.create_fractional_weight({0: 1, 1: 1, 2: 1})

        aw = AdmissibleWeight(("A", 2, 1), weight, level)
        assert aw.cartan_type == ("A", 2, 1)

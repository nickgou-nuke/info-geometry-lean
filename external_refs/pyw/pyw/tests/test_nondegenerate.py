"""
Test suite for pyw.fractional.nondegenerate module
"""

import pytest

from sage.all import RootSystem

from pyw.fractional.nondegenerate import NondegenerateChecker
from pyw.core.weight_space import FractionalWeightSpace


class TestNondegenerateChecker:
    """Test NondegenerateChecker class."""

    def test_init_a2_affine(self):
        """Test initialization with A2 affine type."""
        checker = NondegenerateChecker(["A", 2, 1])
        assert checker.cartan_type == ["A", 2, 1]

    def test_init_a2_finite(self):
        """Test initialization with A2 finite type."""
        checker = NondegenerateChecker(["A", 2])
        assert checker.cartan_type == ["A", 2]
        assert not checker.is_affine

    def test_is_affine_property(self):
        """Test is_affine property."""
        checker_finite = NondegenerateChecker(["A", 2])
        checker_affine = NondegenerateChecker(["A", 2, 1])

        assert not checker_finite.is_affine
        assert checker_affine.is_affine

    def test_setup_creates_root_system(self):
        """Test _setup creates root system."""
        checker = NondegenerateChecker(["A", 2, 1])
        assert checker.root_system is not None
        assert checker.weight_lattice is not None

    def test_simple_coroots(self):
        """Test simple_coroots property."""
        checker = NondegenerateChecker(["A", 2, 1])
        coroots = checker.simple_coroots
        assert len(coroots) >= 2

    def test_is_nondegenerate_with_integer_weight(self):
        """Test is_nondegenerate with integer weight (should be degenerate)."""
        checker = NondegenerateChecker(["A", 2])
        ws = FractionalWeightSpace(["A", 2])

        # Integer weight - likely to have integer pairings
        weight = ws.create_fractional_weight({0: 1, 1: 0})
        result = checker.is_nondegenerate(weight)
        assert isinstance(result, bool)

    def test_is_nondegenerate_with_fractional_weight(self):
        """Test is_nondegenerate with fractional weight."""
        checker = NondegenerateChecker(["A", 2])
        ws = FractionalWeightSpace(["A", 2])

        # Try a fractional weight
        from fractions import Fraction

        weight = ws.create_fractional_weight({0: (1, 2), 1: (1, 3)})
        result = checker.is_nondegenerate(weight)
        assert isinstance(result, bool)

    def test_check_specific_coroots(self):
        """Test check_specific_coroots method."""
        checker = NondegenerateChecker(["A", 2])
        ws = FractionalWeightSpace(["A", 2])

        weight = ws.create_fractional_weight({0: 1, 1: 0})
        coroots = list(checker.simple_coroots.values())

        result = checker.check_specific_coroots(weight, coroots)
        assert isinstance(result, bool)

    def test_compute_pairing(self):
        """Test _compute_pairing method."""
        checker = NondegenerateChecker(["A", 2])
        ws = FractionalWeightSpace(["A", 2])

        weight = ws.create_fractional_weight({0: 1, 1: 0})
        coroot = list(checker.simple_coroots.values())[0]

        pairing = checker._compute_pairing(weight, coroot)
        assert pairing is not None

    def test_is_integer_with_integer(self):
        """Test _is_integer with actual integer."""
        checker = NondegenerateChecker(["A", 2])
        assert checker._is_integer(1) is True
        assert checker._is_integer(0) is True
        assert checker._is_integer(-1) is True

    def test_is_integer_with_fraction(self):
        """Test _is_integer with fraction."""
        checker = NondegenerateChecker(["A", 2])
        from fractions import Fraction

        assert checker._is_integer(Fraction(2, 1)) is True
        assert checker._is_integer(Fraction(3, 2)) is False

    def test_get_failing_coroots(self):
        """Test get_failing_coroots method."""
        checker = NondegenerateChecker(["A", 2])
        ws = FractionalWeightSpace(["A", 2])

        weight = ws.create_fractional_weight({0: 1, 1: 0})
        failing = checker.get_failing_coroots(weight)

        assert isinstance(failing, list)

    def test_is_integer_pairing(self):
        """Test is_integer_pairing convenience method."""
        checker = NondegenerateChecker(["A", 2])
        ws = FractionalWeightSpace(["A", 2])

        weight = ws.create_fractional_weight({0: 1, 1: 0})
        coroot = list(checker.simple_coroots.values())[0]

        result = checker.is_integer_pairing(weight, coroot)
        assert isinstance(result, bool)

    def test_tuple_cartan_type(self):
        """Test with tuple Cartan type."""
        checker = NondegenerateChecker(("A", 2, 1))
        assert checker.cartan_type == ("A", 2, 1)

    def test_multiple_types(self):
        """Test with different Cartan types."""
        types_to_test = [
            ["A", 2],
            ["B", 2],
            ["C", 2],
            ["D", 4],
            ["G", 2],
        ]

        for cartan_type in types_to_test:
            checker = NondegenerateChecker(cartan_type)
            assert checker.root_system is not None
            assert len(checker.simple_coroots) > 0

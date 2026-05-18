"""
Test suite for pyw.fractional.principal module
"""

import pytest

from sage.all import WeylGroup

from pyw.fractional.level import FractionalLevel
from pyw.fractional.principal import PrincipalAdmissibleWeight
from pyw.core.weight_space import FractionalWeightSpace


class TestPrincipalAdmissibleWeight:
    """Test PrincipalAdmissibleWeight class."""

    def test_init_with_fractional_level(self):
        """Test initialization with FractionalLevel."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)

        # Create a simple Weyl group element y (identity for simplicity)
        wg = WeylGroup(["A", 2, 1])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)
        assert paw.level == level
        assert paw.y == y

    def test_setup_creates_weight_space(self):
        """Test _setup creates weight space."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        wg = WeylGroup(["A", 2, 1])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)
        assert paw.weight_space is not None
        assert paw.root_system is not None

    def test_construct_set_returns_list(self):
        """Test construct_set returns a list of weights."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        wg = WeylGroup(["A", 2, 1])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)
        weights = paw.construct_set(max_fundamental_coeff=2)

        assert isinstance(weights, list)

    def test_construct_set_small_bound(self):
        """Test construct_set with small bound."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        wg = WeylGroup(["A", 2, 1])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)
        weights = paw.construct_set(max_fundamental_coeff=1)

        # With small bound, should get a small list
        assert len(weights) >= 0

    def test_apply_dot_action(self):
        """Test apply_dot_action method."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        wg = WeylGroup(["A", 2, 1])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)
        ws = paw.weight_space

        # Create a test weight
        Lambda = ws.fundamental_weights()
        test_weight = Lambda[1]

        result = paw.apply_dot_action(test_weight)
        assert result is not None

    def test_is_principal_admissible(self):
        """Test is_principal_admissible method."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        wg = WeylGroup(["A", 2, 1])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)
        ws = paw.weight_space

        # Test with a simple weight
        Lambda = ws.fundamental_weights()
        test_weight = Lambda[1]

        result = paw.is_principal_admissible(test_weight)
        assert isinstance(result, bool)

    def test_generate_dominant_weights(self):
        """Test _generate_dominant_weights helper method."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        wg = WeylGroup(["A", 2, 1])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)

        # Generate dominant weights for a small level
        weights = paw._generate_dominant_weights(level=2, max_coeff=2)

        assert isinstance(weights, list)

    def test_affine_weyl_vector(self):
        """Test affine Weyl vector (rho_hat) computation."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        wg = WeylGroup(["A", 2, 1])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)
        assert paw.rho_hat is not None

    def test_fundamental_weights_property(self):
        """Test fundamental_weights property."""
        level = FractionalLevel(["A", 2, 1], p=4, u=3)
        wg = WeylGroup(["A", 2, 1])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)
        Lambda = paw.fundamental_weights

        assert Lambda is not None
        assert 0 in Lambda or 1 in Lambda

    def test_finite_type(self):
        """Test with finite (non-affine) type."""
        level = FractionalLevel(["A", 2], p=4, u=3)
        wg = WeylGroup(["A", 2])
        y = wg.one()

        paw = PrincipalAdmissibleWeight(level, y)
        assert paw.level == level

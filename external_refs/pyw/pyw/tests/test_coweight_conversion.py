"""
Tests for coweight to weight conversion.
"""

import pytest
from pyw.core import AffineLieAlgebra
from pyw.core.affine_weight import AffineWeight


def test_coweight_to_weight_basic():
    """Test basic coweight to weight conversion."""
    alg = AffineLieAlgebra(["A", 1, 1])
    Lambda_check = alg.fundamental_coweights()

    # Convert coweight to weight
    cw = -2 * Lambda_check[1]
    w = alg.coweight_to_weight(cw)

    # Should be in finite weight space
    assert w.parent() == alg._finite_root_system.weight_space()

    # Should have same coefficients
    Lambda_finite = alg._finite_root_system.weight_space().fundamental_weights()
    assert w == -2 * Lambda_finite[1]


def test_coweight_to_weight_arithmetic():
    """Test arithmetic operations after conversion."""
    alg = AffineLieAlgebra(["A", 1, 1])
    Lambda_check = alg.fundamental_coweights()

    # Get finite weight
    weight = AffineWeight.affine_fundamental_weight(alg, 0)
    w_finite = weight.finite_part

    # Convert coweight
    cw = -2 * Lambda_check[1]
    cw_as_weight = alg.coweight_to_weight(cw)

    # Should support addition
    result = cw_as_weight + w_finite
    assert result.parent() == w_finite.parent()


def test_coweight_to_weight_fractional():
    """Test fractional coefficient coweights."""
    from sage.all import QQ

    alg = AffineLieAlgebra(["A", 1, 1])

    # Note: Coweight lattice doesn't support fractional coefficients
    # But we can test that the conversion preserves integer coefficients
    # and that the resulting weight can be used with fractional operations
    Lambda_check = alg.fundamental_coweights()

    # Integer coweight
    cw = -4 * Lambda_check[1]
    w = alg.coweight_to_weight(cw)

    # Should preserve integer coefficient
    assert w.monomial_coefficients()[1] == -4

    # Now can do fractional operations on the weight
    fractional_w = w / 3
    assert fractional_w.monomial_coefficients()[1] == QQ(-4) / QQ(3)


def test_coweight_to_weight_different_types():
    """Test conversion for different Cartan types."""
    for cartan_type in [["A", 2, 1], ["B", 2, 1], ["C", 2, 1]]:
        alg = AffineLieAlgebra(cartan_type)
        Lambda_check = alg.fundamental_coweights()

        cw = Lambda_check[1]
        w = alg.coweight_to_weight(cw)

        # Should be in weight space
        assert "Weight space" in str(w.parent())


def test_translation_with_fractional_weight():
    """Test the original notebook use case."""
    alg = AffineLieAlgebra(["A", 1, 1])
    trans = alg.extended_affine_weyl_group().translation

    Lambda_check = alg.fundamental_coweights()
    Lambda = alg.fundamental_weights()

    t_val, u_val = -4, 3

    # This should work
    result = trans(-2 * Lambda_check[1]).action((t_val / u_val) * Lambda[0])

    # Verify result is an AffineWeight
    assert isinstance(result, AffineWeight)

    # Verify level is fractional
    from sage.all import QQ

    assert result.level == QQ(t_val) / QQ(u_val)


def test_coweight_to_weight_finite_parameter():
    """Test finite parameter in coweight_to_weight."""
    alg = AffineLieAlgebra(["A", 2, 1])
    Lambda_check = alg.fundamental_coweights()

    cw = Lambda_check[1]

    # finite=True (default) - should return finite weight space
    w_finite = alg.coweight_to_weight(cw, finite=True)
    assert "['A', 2]" in str(w_finite.parent())  # Finite type

    # finite=False - should return full affine weight space
    w_affine = alg.coweight_to_weight(cw, finite=False)
    assert "['A', 2, 1]" in str(w_affine.parent())  # Affine type


def test_coweight_to_weight_zero():
    """Test conversion of zero coweight."""
    alg = AffineLieAlgebra(["A", 1, 1])
    Lambda_check = alg.fundamental_coweights()

    # Zero coweight
    cw = 0 * Lambda_check[1]
    w = alg.coweight_to_weight(cw)

    # Should be zero in weight space
    assert w == w.parent().zero()


def test_coweight_to_weight_multiple_indices():
    """Test conversion with multiple indices."""
    alg = AffineLieAlgebra(["A", 2, 1])
    Lambda_check = alg.fundamental_coweights()

    # Coweight with multiple indices
    cw = 2 * Lambda_check[1] - 3 * Lambda_check[2]
    w = alg.coweight_to_weight(cw)

    # Check coefficients
    coeffs = w.monomial_coefficients()
    assert coeffs[1] == 2
    assert coeffs[2] == -3

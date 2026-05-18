"""
Tests for AffineLieAlgebra.fundamental_coweights() method.
"""

import pytest


@pytest.mark.sage
def test_fundamental_coweights_basic():
    """Test basic functionality of fundamental_coweights()."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    Lambda_check = ala.fundamental_coweights()

    # Check return type
    assert isinstance(Lambda_check, dict)

    # Check indices (affine A2 has indices 0, 1, 2)
    assert sorted(Lambda_check.keys()) == [0, 1, 2]

    # Check parent lattice
    assert "Coweight lattice" in str(Lambda_check[0].parent())


@pytest.mark.sage
def test_fundamental_coweights_finite():
    """Test fundamental_coweights(finite=True) for affine types."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])

    # Full coweight lattice (includes index 0)
    Lambda_check_full = ala.fundamental_coweights(finite=False)
    assert sorted(Lambda_check_full.keys()) == [0, 1, 2]

    # Finite coweight lattice (only indices 1, 2)
    Lambda_check_finite = ala.fundamental_coweights(finite=True)
    assert sorted(Lambda_check_finite.keys()) == [1, 2]

    # Check they come from different lattices
    assert "['A', 2, 1]" in str(Lambda_check_full[0].parent())
    assert "['A', 2]" in str(Lambda_check_finite[1].parent())


@pytest.mark.sage
def test_fundamental_coweights_with_extended_weyl_group():
    """Test that finite coweights work with ExtendedAffineWeylGroup."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    Lambda_check_finite = ala.fundamental_coweights(finite=True)
    W_ext = ala.extended_affine_weyl_group()

    # Should be able to create translations
    t1 = W_ext.translation(Lambda_check_finite[1])
    t2 = W_ext.translation(Lambda_check_finite[2])

    assert "Lambdacheck[1]" in str(t1)
    assert "Lambdacheck[2]" in str(t2)


@pytest.mark.sage
def test_fundamental_coweights_different_types():
    """Test fundamental_coweights() for different Cartan types."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    # Test B2^(1)
    ala_b2 = AffineLieAlgebra(["B", 2, 1])
    Lambda_check_b2 = ala_b2.fundamental_coweights()
    assert sorted(Lambda_check_b2.keys()) == [0, 1, 2]

    # Test G2^(1)
    ala_g2 = AffineLieAlgebra(["G", 2, 1])
    Lambda_check_g2 = ala_g2.fundamental_coweights()
    assert sorted(Lambda_check_g2.keys()) == [0, 1, 2]


@pytest.mark.sage
def test_fundamental_coweights_finite_type():
    """Test fundamental_coweights() for finite Cartan types."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    # For finite types, finite=True should have no effect
    ala = AffineLieAlgebra(["A", 2])
    Lambda_check = ala.fundamental_coweights()
    Lambda_check_finite = ala.fundamental_coweights(finite=True)

    assert sorted(Lambda_check.keys()) == [1, 2]
    assert sorted(Lambda_check_finite.keys()) == [1, 2]

    # Same parent
    assert Lambda_check[1].parent() == Lambda_check_finite[1].parent()

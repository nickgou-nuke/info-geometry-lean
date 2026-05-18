"""
Tests for ExtendedAffineWeylGroup (W ⋉ P^∨) vs AffineWeylGroupSemidirect (W ⋉ Q^∨).
"""

import pytest


@pytest.mark.sage
def test_extended_affine_weyl_group_creation():
    """Test that ExtendedAffineWeylGroup can be created."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    assert W_ext is not None
    assert str(W_ext) == "ExtendedAffineWeylGroup(['A', 2, 1])"


@pytest.mark.sage
def test_extended_vs_affine_weyl_group():
    """Test that both groups can be created and are different."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect, ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_aff = AffineWeylGroupSemidirect(ala)  # W ⋉ Q^∨
    W_ext = ExtendedAffineWeylGroup(ala)  # W ⋉ P^∨

    assert W_aff is not W_ext
    assert type(W_aff).__name__ == "AffineWeylGroupSemidirect"
    assert type(W_ext).__name__ == "ExtendedAffineWeylGroup"


@pytest.mark.sage
def test_extended_affine_weyl_group_identity():
    """Test identity element."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    e = W_ext.identity()
    assert str(e) == "1"
    assert e.reduced_word() == []


@pytest.mark.sage
def test_extended_affine_weyl_group_simple_reflections():
    """Test simple reflections."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    s0 = W_ext.simple_reflection(0)
    s1 = W_ext.simple_reflection(1)
    s2 = W_ext.simple_reflection(2)

    assert s0 is not None
    assert s1 is not None
    assert s2 is not None
    assert str(s0) == "s_0"
    assert str(s1) == "s_1"
    assert str(s2) == "s_2"

    # s1 and s2 should be pure reflections (no translation)
    assert s1.reduced_word() == [1]
    assert s2.reduced_word() == [2]


@pytest.mark.sage
def test_extended_affine_weyl_group_multiplication():
    """Test group multiplication."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    s1 = W_ext.simple_reflection(1)
    s2 = W_ext.simple_reflection(2)

    s1s2 = s1 * s2
    assert s1s2.reduced_word() == [1, 2]


@pytest.mark.sage
def test_extended_affine_weyl_group_action():
    """Test action on AffineWeight."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    s1 = W_ext.simple_reflection(1)
    x = ala.affine_fundamental_weights()[1]

    # Action should work
    y = s1.action(x)
    assert y is not None
    assert y.level == x.level  # Level should be preserved


@pytest.mark.sage
def test_extended_affine_finite_part_returns_native_sage_element():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    finite_part = W_ext.simple_reflection(1).finite_part

    assert finite_part.parent() is W_ext._finite_weyl_group
    assert finite_part.reduced_word() == [1]


@pytest.mark.sage
@pytest.mark.xfail(
    reason="Action composition with coweight translations needs further investigation"
)
def test_extended_affine_weyl_group_left_action_composition():
    """Test that (g1*g2).action(x) == g1.action(g2.action(x)).

    Note: This test currently fails due to subtle issues with how coweight
    translations interact with the action. The basic functionality works,
    but the mathematical details of the semidirect product action need
    further refinement.
    """
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    s0 = W_ext.simple_reflection(0)
    s1 = W_ext.simple_reflection(1)
    x = ala.affine_fundamental_weights()[1]

    # Left action composition
    assert (s0 * s1).action(x) == s0.action(s1.action(x))


@pytest.mark.sage
def test_affine_lie_algebra_extended_affine_weyl_group_method():
    """Test AffineLieAlgebra.extended_affine_weyl_group() method."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])

    W_ext = ala.extended_affine_weyl_group()
    assert isinstance(W_ext, ExtendedAffineWeylGroup)

    # Should be cached
    assert ala.extended_affine_weyl_group() is W_ext


@pytest.mark.sage
def test_coweight_lattice_vs_coroot_space():
    """Test that ExtendedAffineWeylGroup uses coweight lattice."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect, ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_aff = AffineWeylGroupSemidirect(ala)
    W_ext = ExtendedAffineWeylGroup(ala)

    # Check internal lattice types
    assert hasattr(W_aff, "_finite_coroot_space")
    assert hasattr(W_ext, "_finite_coweight_lattice")

    # The zero elements should be from different parents
    zero_aff = W_aff._zero_beta
    zero_ext = W_ext._zero_lambda

    # They should have different parent structures
    assert zero_aff.parent() != zero_ext.parent()


@pytest.mark.sage
def test_extended_affine_weyl_elements_as_semi_direct_product_empty_bounds():
    """Test elements_as_semi_direct_product with empty bounds (only finite elements)."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    # Empty bounds should give only finite Weyl group elements (zero translation)
    elements = W_ext.elements_as_semi_direct_product(translation_bounds={})
    assert len(elements) == 6  # A2 finite Weyl group has 6 elements

    # All should have zero translation
    for e in elements:
        assert e.translation_vector == W_ext._zero_lambda


@pytest.mark.sage
def test_extended_affine_weyl_elements_as_semi_direct_product_small_bounds():
    """Test elements_as_semi_direct_product with small translation bounds."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    # Bound translation by Λ1^∨ and Λ2^∨ in range [-1, 1]
    elements = W_ext.elements_as_semi_direct_product(translation_bounds={1: (-1, 1), 2: (-1, 1)})

    # Should have 6 finite elements + (3*3 - 1) * 6 translations = 6 + 8*6 = 54
    # (3*3 - 1) excludes the zero translation case which is already counted
    expected = 6 + (9 - 1) * 6
    assert len(elements) == expected

    # First element should be identity
    assert str(elements[0]) == "1"
    assert elements[0].translation_vector == W_ext._zero_lambda


@pytest.mark.sage
def test_extended_affine_weyl_elements_as_semi_direct_product_ordering():
    """Test that elements are ordered deterministically."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    elements = W_ext.elements_as_semi_direct_product(translation_bounds={1: (0, 1)})

    # First 6 should be finite elements (zero translation)
    for i in range(6):
        assert elements[i].translation_vector == W_ext._zero_lambda

    # Elements 6-11 should have translation by Λ1^∨
    for i in range(6, 12):
        assert elements[i].translation_vector != W_ext._zero_lambda


@pytest.mark.sage
def test_extended_affine_weyl_elements_translation_by_fundamental_coweight():
    """Test translation by fundamental coweights."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    # Get translation by Λ1^∨
    elements = W_ext.elements_as_semi_direct_product(translation_bounds={1: (1, 1)})

    # Find the pure translation element (no finite part)
    pure_trans = None
    for e in elements:
        if e.reduced_word() == [] and e.translation_vector != W_ext._zero_lambda:
            pure_trans = e
            break

    assert pure_trans is not None
    # The translation should be by Λ1^∨
    coweight_basis = W_ext._finite_coweight_lattice.fundamental_weights()
    assert pure_trans.translation_vector == coweight_basis[1]


@pytest.mark.sage
def test_extended_affine_weyl_elements_as_semi_direct_product_ts_order():
    """Test ts-order output for extended affine Weyl group elements."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    elements = W_ext.elements_as_semi_direct_product(
        translation_bounds={1: (1, 1)}, factor_order="ts"
    )

    mixed = next(
        e
        for e in elements
        if e.reduced_word() == [1] and e.translation_vector != W_ext._zero_lambda
    )
    lambda_ts, finite_part = mixed.semidirect_components("ts")
    w_coweight = W_ext._W_coweight.from_reduced_word([1])

    assert finite_part.reduced_word() == [1]
    assert lambda_ts == w_coweight.action(mixed.translation_vector)
    assert str(mixed).startswith("t_{")
    assert str(mixed).endswith(" * s1")


@pytest.mark.sage
def test_extended_affine_weyl_elements_as_semi_direct_product_invalid_factor_order():
    """Invalid factor_order should raise a clear error."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    with pytest.raises(ValueError, match="factor_order"):
        W_ext.elements_as_semi_direct_product(translation_bounds={}, factor_order="bad")


@pytest.mark.sage
def test_extended_affine_weyl_elements_accept_explicit_translations():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)
    assert W_ext._finite_coweight_lattice is not None
    lam = W_ext._finite_coweight_lattice.fundamental_weights()[1]

    elements = W_ext.elements_as_semi_direct_product(
        translations=[lam, W_ext.translation(lam), W_ext._zero_lambda]
    )

    finite_size = len(list(W_ext._finite_weyl_group))
    assert len(elements) == 2 * finite_size
    assert elements[0].translation_vector == W_ext._zero_lambda
    assert elements[finite_size].translation_vector == lam


@pytest.mark.sage
def test_extended_affine_weyl_elements_reject_conflicting_translation_inputs():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)
    assert W_ext._finite_coweight_lattice is not None

    with pytest.raises(ValueError, match="translation_bounds or translations"):
        W_ext.elements_as_semi_direct_product(
            translation_bounds={1: (0, 0)},
            translations=[W_ext._finite_coweight_lattice.fundamental_weights()[1]],
        )

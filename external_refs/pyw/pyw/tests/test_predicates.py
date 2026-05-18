from sage.all import QQ

from pyw.core.affine_lie_algebra import AffineLieAlgebra
from pyw.core.affine_weight import AffineWeight
from pyw.utils.predicates import (
    is_affine_root,
    is_finite_root,
    is_positive_affine_root,
    is_positive_finite_root,
    is_positive_real_affine_root,
    is_real_affine_root,
    is_simple_root,
    is_zero_weight,
)


def test_positive_affine_roots_convention():
    ala = AffineLieAlgebra(["A", 2, 1])

    alpha_hat_1 = AffineWeight.affine_simple_root(ala, 1)  # (alpha_1; 0; 0)
    delta = AffineWeight.delta(ala)  # (0; 0; 1)
    minus_alpha_hat_1 = -alpha_hat_1

    assert is_affine_root(alpha_hat_1)
    assert is_affine_root(delta)
    assert is_affine_root(minus_alpha_hat_1)

    assert is_positive_affine_root(alpha_hat_1)
    assert is_positive_affine_root(delta)

    assert not is_positive_affine_root(minus_alpha_hat_1)
    # n>0 is positive only if alpha is a root (or alpha=0)
    assert is_positive_affine_root(minus_alpha_hat_1 + 1 * delta)
    assert not is_positive_affine_root((2 * alpha_hat_1) + 1 * delta)


def test_real_affine_roots_convention():
    ala = AffineLieAlgebra(["A", 2, 1])

    alpha_hat_1 = AffineWeight.affine_simple_root(ala, 1)
    delta = AffineWeight.delta(ala)

    assert is_real_affine_root(alpha_hat_1)
    assert not is_real_affine_root(delta)
    assert is_real_affine_root(alpha_hat_1 + delta)
    assert not is_real_affine_root((2 * alpha_hat_1) + delta)

    assert is_positive_real_affine_root(alpha_hat_1)
    assert is_positive_real_affine_root(alpha_hat_1 + delta)


def test_finite_root_for_affineweight():
    ala = AffineLieAlgebra(["A", 2, 1])
    alpha_hat_1 = AffineWeight.affine_simple_root(ala, 1)
    assert is_finite_root(alpha_hat_1)
    assert is_positive_finite_root(alpha_hat_1)

    assert not is_finite_root(2 * alpha_hat_1)


def test_simple_root():
    ala = AffineLieAlgebra(["A", 2, 1])
    alpha_hat_0 = AffineWeight.affine_simple_root(ala, 0)
    alpha_hat_1 = AffineWeight.affine_simple_root(ala, 1)
    assert is_simple_root(alpha_hat_0)
    assert is_simple_root(alpha_hat_1)


def test_zero_weight():
    ala = AffineLieAlgebra(["A", 2, 1])
    assert is_zero_weight(AffineWeight.zero(ala))

    finite_zero = ala._finite_root_system.weight_space().zero()
    assert is_zero_weight(finite_zero)


def test_positive_finite_root_for_sage_root():
    ala = AffineLieAlgebra(["A", 2, 1])
    rs = ala._finite_root_system.root_space()
    alpha = rs.simple_roots()
    assert is_positive_finite_root(alpha[1], algebra=ala)
    assert not is_positive_finite_root(-alpha[1], algebra=ala)


def test_finite_root_requires_membership_not_scaling():
    ala = AffineLieAlgebra(["A", 2, 1])
    rs = ala._finite_root_system.root_space()
    alpha = rs.simple_roots()[1]
    assert is_finite_root(alpha, algebra=ala)
    assert is_finite_root(-alpha, algebra=ala)
    assert not is_finite_root(2 * alpha, algebra=ala)

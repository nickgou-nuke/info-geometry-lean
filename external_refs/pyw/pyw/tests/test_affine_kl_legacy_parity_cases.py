from itertools import product

import pytest
from sage.all import QQ


def _coeff_tuple(ala, beta):
    idxs = [int(i) for i in ala.affine_weyl_group()._finite_coroot_space.index_set()]
    coeffs = beta.monomial_coefficients()
    return tuple(int(coeffs.get(i, 0)) for i in idxs)


def _neg_shift_formula(weight, beta):
    lam_amb = weight.finite_part.to_ambient()
    beta_amb = beta.to_ambient()
    pairing = QQ(lam_amb.inner_product(beta_amb))
    beta_norm_sq = QQ(beta_amb.inner_product(beta_amb))
    return pairing + QQ(weight.level) * beta_norm_sq / QQ(2)


@pytest.mark.sage
@pytest.mark.parametrize(
    "cartan, coeff, index, order, box_radius",
    [
        (["A", 2, 1], -2, 0, 6, 6),
        (["A", 2, 1], -2, 1, 6, 6),
        (["A", 2, 1], -1, 2, 6, 6),
        (["A", 2, 1], 2, 1, 6, 6),
    ],
)
def test_affine_kl_context_translation_set_satisfies_exact_nshift_inequality(
    cartan, coeff, index, order, box_radius
):
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.character import KazhdanLusztigCharacter

    ala = AffineLieAlgebra(cartan)
    kl_char = KazhdanLusztigCharacter(ala)
    fw = ala.fundamental_weights()
    lam = coeff * fw[index]

    context = kl_char.prepare_data(lam, order=order)
    selected_weight = context.Lambda_hat + ala.affine_rho()
    max_neg_shift = QQ(order) + QQ(selected_weight.grade)

    semidirect = ala.affine_weyl_group()
    idxs = [int(i) for i in semidirect._finite_coroot_space.index_set()]
    basis = semidirect._finite_coroot_space.simple_roots()

    expected = set()
    for coeffs in product(range(-box_radius, box_radius + 1), repeat=len(idxs)):
        beta = semidirect._zero_beta
        for i, c in zip(idxs, coeffs):
            if c:
                beta += int(c) * basis[i]
        neg_shift = _neg_shift_formula(selected_weight, beta)
        if QQ(0) <= neg_shift <= max_neg_shift:
            expected.add(tuple(int(c) for c in coeffs))

    got = {_coeff_tuple(ala, t.translation_vector) for t in context.translations}
    assert expected.issubset(got)
    assert got

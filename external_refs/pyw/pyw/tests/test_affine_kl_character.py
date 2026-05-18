import pytest


@pytest.mark.sage
def test_kl_character_builds_context():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.affine_weight import AffineWeight
    from pyw.core.character import KazhdanLusztigCharacter

    ala = AffineLieAlgebra(["A", 2, 1])
    lam = AffineWeight.affine_fundamental_weight(ala, 1)
    kl_char = KazhdanLusztigCharacter(ala)

    context = kl_char.prepare_data(lam, order=1)

    assert context.Lambda_hat.is_dominant()
    assert context.quotient_representatives


@pytest.mark.sage
def test_kl_character_numerator_terms_are_available():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.affine_weight import AffineWeight
    from pyw.core.character import KazhdanLusztigCharacter

    ala = AffineLieAlgebra(["A", 2, 1])
    lam = AffineWeight.affine_fundamental_weight(ala, 1)
    kl_char = KazhdanLusztigCharacter(ala)

    terms = kl_char.numerator_terms(lam, order=1)

    assert terms
    assert all(term.coefficient != 0 for term in terms)


@pytest.mark.sage
def test_kl_character_returns_formal_character():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.affine_weight import AffineWeight
    from pyw.core.character import FormalCharacter, KazhdanLusztigCharacter

    ala = AffineLieAlgebra(["A", 2, 1])
    lam = AffineWeight.affine_fundamental_weight(ala, 1)
    kl_char = KazhdanLusztigCharacter(ala)

    ch = kl_char.character(lam, order=1)

    assert isinstance(ch, FormalCharacter)
    assert ch.max_grade == 1
    assert ch[0] != 0


@pytest.mark.sage
def test_kl_character_numerator_terms_accept_explicit_translations():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.affine_weight import AffineWeight
    from pyw.core.character import KazhdanLusztigCharacter

    ala = AffineLieAlgebra(["A", 2, 1])
    lam = AffineWeight.affine_fundamental_weight(ala, 1)
    kl_char = KazhdanLusztigCharacter(ala)
    beta = ala.affine_weyl_group()._finite_coroot_space.simple_roots()[1]

    terms = kl_char.numerator_terms(lam, order=1, translations=[0, beta])

    assert terms
    assert all(term.coefficient != 0 for term in terms)

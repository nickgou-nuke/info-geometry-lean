import pytest


# Test multiple Cartan types to ensure equations hold universally
AFFINE_CARTAN_TYPES = [
    ["A", 2, 1],  # A2^(1) - simply laced
    ["A", 3, 1],  # A3^(1) - simply laced, higher rank
    ["B", 2, 1],  # B2^(1) - non-simply laced
    ["C", 2, 1],  # C2^(1) - non-simply laced
    ["D", 4, 1],  # D4^(1) - simply laced with triality
    ["G", 2, 1],  # G2^(1) - exceptional, non-simply laced
    ["F", 4, 1],  # F4^(1) - exceptional
    ["E", 6, 1],  # E6^(1) - exceptional, simply laced
]


def _to_sage_domain_weight(sage_domain, affine_weight):
    from sage.all import QQ, vector

    sage_weight = affine_weight.to_sagemath()
    coords = list(sage_weight.to_vector()) + [affine_weight.grade]
    return sage_domain.from_vector(vector(QQ, coords))


@pytest.mark.sage
@pytest.mark.parametrize("simple_index", [0, 1])
def test_word_and_reduced_word_interfaces_for_simple_reflections(simple_index):
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(["A", 2, 1])
    W = AffineWeylGroupSemidirect(ala)

    element = W.simple_reflection(simple_index)
    sage_group = ala.affine_weyl_group_sage()

    assert element.word() == (simple_index,)
    assert element.reduced_word_list() == [simple_index]
    assert element.reduced_word() == sage_group.from_reduced_word([simple_index])
    assert str(element) == f"s_{simple_index}"


@pytest.mark.sage
@pytest.mark.parametrize(("coeff", "negative"), [(1, False), (-1, True)])
def test_translation_word_list_preserves_simple_coroot_sign_a4(coeff, negative):
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(["A", 4, 1])
    W = AffineWeylGroupSemidirect(ala)
    beta = W._finite_coroot_space.simple_roots()[1]

    element = W.translation(coeff * beta)

    assert element.word() == W.simple_translation_word_list(1, negative=negative)
    assert element.word() != W.simple_translation_word_list(1, negative=not negative)


@pytest.mark.sage
@pytest.mark.parametrize("coeff", [1, -1])
def test_word_translation_sign_matches_intended_translation_a4(coeff):
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(["A", 4, 1])
    W = AffineWeylGroupSemidirect(ala)
    beta = W._finite_coroot_space.simple_roots()[1]

    element = W.translation(coeff * beta)
    opposite = W.translation(-coeff * beta)

    assert element.word() == W.simple_translation_word_list(1, negative=(coeff < 0))
    assert element.word() != opposite.word()


@pytest.mark.sage
def test_reduced_word_interfaces_for_composite_element():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(["A", 2, 1])
    W = AffineWeylGroupSemidirect(ala)

    beta = W._finite_coroot_space.simple_roots()[1]
    element = W.simple_reflection(1) * W.translation(beta)
    sage_group = ala.affine_weyl_group_sage()
    expected = [int(i) for i in sage_group.from_reduced_word(list(element.word())).reduced_word()]

    assert element.reduced_word_list() == expected
    assert element.reduced_word() == sage_group.from_reduced_word(expected)


@pytest.mark.sage
@pytest.mark.parametrize("cartan_type", AFFINE_CARTAN_TYPES)
def test_extended_affine_weyl_left_action_composition(cartan_type):
    """(g1*g2).action(x) == g1.action(g2.action(x)) for all affine types."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(cartan_type)
    W = AffineWeylGroupSemidirect(ala)
    root_system = ala.root_system()
    assert root_system is not None

    # Test with s0 and s1
    s0 = W.simple_reflection(0)
    s1 = W.simple_reflection(1)
    x = ala.affine_fundamental_weights()[1]

    assert (s0 * s1).action(x) == s0.action(s1.action(x))

    # Test with other combinations if rank >= 2
    index_set = list(root_system.index_set())
    if len([i for i in index_set if i != 0]) >= 2:
        finite_indices = [i for i in index_set if i != 0]
        i1, i2 = finite_indices[0], finite_indices[1]
        si1 = W.simple_reflection(i1)
        si2 = W.simple_reflection(i2)

        assert (si1 * si2).action(x) == si1.action(si2.action(x))


@pytest.mark.sage
@pytest.mark.parametrize("cartan_type", AFFINE_CARTAN_TYPES)
def test_extended_affine_weyl_s0_decomposition_matches_action(cartan_type):
    """s0 = s_theta * t_{-theta^vee} for all affine types."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(cartan_type)
    W = AffineWeylGroupSemidirect(ala)
    root_system = ala.root_system()
    assert root_system is not None

    s0 = W.simple_reflection(0)
    x = ala.affine_fundamental_weights()[0]

    # manual: apply translation then finite reflection
    t = W.translation(-W.theta_coroot())
    manual = W._s_theta_weight.action(t.action(x).finite_part)
    expected = x.__class__(x.algebra, manual, x.level, t.action(x).grade)

    assert s0.action(x) == expected


@pytest.mark.sage
@pytest.mark.parametrize("cartan_type", AFFINE_CARTAN_TYPES)
def test_translation_grade_uses_weight_coroot_pairing(cartan_type):
    """Translation shifts grade by -(<λ,β> + k|β|^2/2) for all affine types."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(cartan_type)
    W = AffineWeylGroupSemidirect(ala)
    root_system = ala.root_system()
    assert root_system is not None

    # Test with first non-zero fundamental weight
    index_set = list(root_system.index_set())
    finite_indices = [i for i in index_set if i != 0]
    test_index = finite_indices[0] if finite_indices else 1

    x = ala.affine_fundamental_weights()[test_index]

    # Test with a simple coroot
    simple_coroots = W._finite_coroot_space.simple_roots()
    beta = simple_coroots[test_index]
    t = W.translation(beta)

    y = t.action(x)

    # expected pairing and norm are computed in ambient space
    pairing = x.finite_part.to_ambient().inner_product(beta.to_ambient())
    norm_sq = beta.norm_squared()
    expected_grade = x.grade - pairing - x.level * norm_sq / 2

    assert y.grade == expected_grade

    # Test with negative coroot as well
    beta_neg = -beta
    t_neg = W.translation(beta_neg)
    y_neg = t_neg.action(x)

    pairing_neg = x.finite_part.to_ambient().inner_product(beta_neg.to_ambient())
    norm_sq_neg = beta_neg.norm_squared()
    expected_grade_neg = x.grade - pairing_neg - x.level * norm_sq_neg / 2

    assert y_neg.grade == expected_grade_neg


@pytest.mark.sage
@pytest.mark.parametrize("cartan_type", AFFINE_CARTAN_TYPES)
def test_reflection_for_arbitrary_root(cartan_type):
    """W.reflection(root) gives s_α as (s_α, 0) for any positive root."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(cartan_type)
    W = AffineWeylGroupSemidirect(ala)

    root_lattice = W._finite_root_lattice
    positive_roots = list(root_lattice.positive_roots())

    x = ala.affine_fundamental_weights()[1]

    for alpha in positive_roots:
        s_alpha = W.reflection(alpha)

        # 1. Check it is a pure finite reflection (no translation)
        assert s_alpha.translation_vector == W._zero_beta

        # 2. Check s_α is an involution: s_α * s_α = identity
        s_sq = s_alpha * s_alpha
        assert list(s_sq._w.reduced_word()) == []
        assert s_sq.translation_vector == W._zero_beta

        # 3. Action composition: (s_α * s_α)(x) == x
        assert s_sq.action(x) == x

    # 4. Specifically check that reflection(theta) matches s_theta
    theta = root_lattice.highest_root()
    s_theta = W.reflection(theta)
    s0 = W.simple_reflection(0)
    t_neg_theta = W.translation(-W.theta_coroot())
    s_theta_via_s0 = s0 * W.translation(W.theta_coroot())

    # s_theta.action == s_theta_via_s0.action on test weight
    assert s_theta.action(x) == s_theta_via_s0.action(x)


@pytest.mark.sage
@pytest.mark.parametrize("cartan_type", AFFINE_CARTAN_TYPES)
def test_reflection_matches_simple_reflection(cartan_type):
    """W.reflection(α_i) should give the same action as W.simple_reflection(i)."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(cartan_type)
    W = AffineWeylGroupSemidirect(ala)

    root_lattice = W._finite_root_lattice
    simple_roots = root_lattice.simple_roots()
    x = ala.affine_fundamental_weights()[1]

    for i, alpha_i in simple_roots.items():
        s_i = W.simple_reflection(int(i))
        s_alpha_i = W.reflection(alpha_i)
        assert s_alpha_i.action(x) == s_i.action(x)


@pytest.mark.sage
@pytest.mark.parametrize("cartan_type", AFFINE_CARTAN_TYPES)
def test_affine_root_reflection_matches_algebra_formula(cartan_type):
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(cartan_type)
    W = AffineWeylGroupSemidirect(ala)

    alpha_hat = ala.affine_simple_roots()[0]
    x = ala.affine_fundamental_weights()[1]

    reflected = W.reflection(alpha_hat)
    expected = ala.affine_weyl_reflection(alpha_hat, x)

    assert reflected.action(x) == expected


@pytest.mark.sage
def test_affine_root_associated_reflection_word_matches_reflection_action():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect

    ala = AffineLieAlgebra(["A", 2, 1])
    W = AffineWeylGroupSemidirect(ala)

    alpha_hat = ala.affine_simple_roots()[1] + ala.affine_delta()
    x = ala.affine_fundamental_weights()[1]

    word = W.associated_reflection_word(alpha_hat)
    reflected = W.associated_reflection(alpha_hat)

    assert reflected.word() == tuple(word)
    assert reflected.reduced_word_list() == [int(i) for i in ala.affine_weyl_group_sage().from_reduced_word(list(word)).reduced_word()]
    assert reflected.action(x) == ala.affine_weyl_reflection(alpha_hat, x)


@pytest.mark.sage
def test_affine_weight_associated_reflection_method():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    alpha_hat = ala.affine_simple_roots()[1] + ala.affine_delta()

    assert alpha_hat.associated_reflection() == ala.affine_weyl_group().associated_reflection_word(
        alpha_hat
    )


@pytest.mark.sage
def test_affine_plus_delta_reflection_word_list_uses_pyw_associated_reflection():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    W = ala.affine_weyl_group()

    expected = ala.affine_simple_roots()[1].associated_reflection()
    expected = (ala.affine_simple_roots()[1] + ala.affine_delta()).associated_reflection()

    assert W.affine_plus_delta_reflection_word_list(1) == expected


@pytest.mark.sage
def test_translation_times_reflection_a2():
    """t_{ω1+3ω2} * s_θ in ExtendedAffineWeylGroup for A2."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import ExtendedAffineWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])
    W_ext = ExtendedAffineWeylGroup(ala)

    coweights = W_ext._finite_coweight_lattice.fundamental_weights()
    vec = coweights[1] + 3 * coweights[2]
    t_vec = W_ext.translation(vec)

    s_theta = W_ext.reflection(W_ext._finite_root_lattice.highest_root())

    result = t_vec * s_theta
    # s_θ(ω1∨ + 3ω2∨) = (ω1∨+3ω2∨) - 4(ω1∨+ω2∨) = -3ω1∨ - ω2∨
    expected_translation = -3 * coweights[1] - coweights[2]

    assert result.translation_vector == expected_translation
    # finite part is s_theta = s1*s2*s1
    assert sorted(result.finite_part.reduced_word()) == [1, 1, 2] or len(result.finite_part.reduced_word()) == 3


@pytest.mark.sage
def test_affine_lie_algebra_affine_weyl_group_glue():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra
    from pyw.core.weyl_group import AffineWeylGroupSemidirect, FiniteWeylGroup

    ala = AffineLieAlgebra(["A", 2, 1])

    W_hat = ala.affine_weyl_group()
    assert isinstance(W_hat, AffineWeylGroupSemidirect)
    # cached
    assert ala.affine_weyl_group() is W_hat

    W = ala.finite_weyl_group()
    assert isinstance(W, FiniteWeylGroup)
    assert ala.finite_weyl_group() is W


@pytest.mark.sage
def test_affine_semidirect_finite_part_returns_native_sage_element():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    W = ala.affine_weyl_group()

    finite_part = W.simple_reflection(1).finite_part

    assert finite_part.parent() is W._finite_weyl_group
    assert finite_part.reduced_word() == [1]


@pytest.mark.sage
def test_affine_weyl_elements_as_semi_direct_product_ts_order():
    """Test ts-order output for affine semidirect-product elements."""
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    W = ala.affine_weyl_group()

    elements = W.elements_as_semi_direct_product(translation_bounds={1: (1, 1)}, factor_order="ts")

    mixed = next(
        e for e in elements if e.finite_part.reduced_word() == [1] and e.translation_vector != W._zero_beta
    )
    beta_ts, finite_part = mixed.semidirect_components("ts")
    w_coroot = W._W_coroot.from_reduced_word([1])

    assert finite_part.reduced_word() == [1]
    assert beta_ts == w_coroot.action(mixed.translation_vector)
    assert str(mixed).startswith("t_{")
    assert "* s" in str(mixed)


@pytest.mark.sage
def test_affine_weyl_elements_as_semi_direct_product_accepts_explicit_translations():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    W = ala.affine_weyl_group()
    assert W._finite_coroot_space is not None
    beta = W._finite_coroot_space.simple_roots()[1]

    elements = W.elements_as_semi_direct_product(translations=[beta, W.translation(beta), 0])

    finite_size = len(list(W._finite_weyl_group))
    assert len(elements) == 2 * finite_size
    assert elements[0].translation_vector == W._zero_beta
    assert elements[finite_size].translation_vector == beta


@pytest.mark.sage
def test_affine_weyl_elements_as_semi_direct_product_rejects_conflicting_translation_inputs():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    W = ala.affine_weyl_group()
    assert W._finite_coroot_space is not None

    with pytest.raises(ValueError, match="translation_bounds or translations"):
        W.elements_as_semi_direct_product(
            translation_bounds={1: (0, 0)},
            translations=[W._finite_coroot_space.simple_roots()[1]],
        )


@pytest.mark.sage
def test_semidirect_translation_affine_word_is_nonempty():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    W = ala.affine_weyl_group()
    beta = W._finite_coroot_space.simple_roots()[1]

    translation = W.translation(beta)

    assert tuple(translation.word())


@pytest.mark.sage
def test_semidirect_inverse_undoes_action():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    W = ala.affine_weyl_group()
    x = ala.affine_fundamental_weights()[1]

    g = W.simple_reflection(0) * W.translation(W._finite_coroot_space.simple_roots()[1])
    g_inv = g.inverse()

    assert g_inv.action(g.action(x)) == x


@pytest.mark.sage
def test_semidirect_bruhat_le_matches_sage_affine_group():
    from pyw.core.affine_lie_algebra import AffineLieAlgebra

    ala = AffineLieAlgebra(["A", 2, 1])
    W = ala.affine_weyl_group()

    x = W.simple_reflection(1)
    y = W.simple_reflection(1) * W.simple_reflection(2)

    assert x.bruhat_le(y) == bool(x.reduced_word().bruhat_le(y.reduced_word()))

    # 支持 tuple/list 输入路径
    y_word = tuple(int(i) for i in y.word())
    assert x.bruhat_le(y_word) == bool(x.reduced_word().bruhat_le(y.reduced_word()))

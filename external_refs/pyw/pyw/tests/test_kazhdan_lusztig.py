"""
Tests for Kazhdan-Lusztig character computation modules.

These tests verify:
- Bruhat order comparisons
- KL polynomial computation
- Formal character arithmetic
- Kac-Wakimoto character formula
"""

import json

import pytest
from sage.all import QQ, WeylGroup


class TestBruhatOrder:
    """Tests for BruhatOrder class."""

    def test_bruhat_le_identity(self):
        """Identity is less than or equal to any element."""
        from pyw.core.bruhat import BruhatOrder

        W = WeylGroup(["A", 2])
        bruhat = BruhatOrder(W)

        e = W.one()
        s1 = W.simple_reflection(1)
        s2 = W.simple_reflection(2)

        assert bruhat.le(e, e)
        assert bruhat.le(e, s1)
        assert bruhat.le(e, s2)
        assert bruhat.le(e, s1 * s2)

    def test_bruhat_le_simple_reflections(self):
        """Simple reflections are comparable with products."""
        from pyw.core.bruhat import BruhatOrder

        W = WeylGroup(["A", 2])
        bruhat = BruhatOrder(W)

        s1 = W.simple_reflection(1)
        s2 = W.simple_reflection(2)

        assert bruhat.le(s1, s1 * s2)
        assert bruhat.le(s2, s1 * s2)
        assert not bruhat.le(s1 * s2, s1)

    def test_bruhat_interval_A2(self):
        """Bruhat interval [e, w0] contains all elements for A2."""
        from pyw.core.bruhat import BruhatOrder

        W = WeylGroup(["A", 2])
        bruhat = BruhatOrder(W)

        e = W.one()
        w0 = W.long_element()

        interval = bruhat.interval(e, w0)
        assert len(interval) == 6  # |S_3| = 6

    def test_length_function(self):
        """Length function returns correct values."""
        from pyw.core.bruhat import BruhatOrder

        W = WeylGroup(["A", 2])
        bruhat = BruhatOrder(W)

        e = W.one()
        s1 = W.simple_reflection(1)
        w0 = W.long_element()

        assert bruhat.length(e) == 0
        assert bruhat.length(s1) == 1
        assert bruhat.length(w0) == 3  # Longest element in S_3


class TestParabolicSubgroup:
    """Tests for ParabolicSubgroup class."""

    def test_parabolic_contains(self):
        """Parabolic subgroup membership test."""
        from pyw.core.bruhat import BruhatOrder

        W = WeylGroup(["A", 3])
        bruhat = BruhatOrder(W)

        W_I = bruhat.parabolic_subgroup({1, 2})

        s1 = W.simple_reflection(1)
        s2 = W.simple_reflection(2)
        s3 = W.simple_reflection(3)

        assert W_I.contains(s1)
        assert W_I.contains(s2)
        assert W_I.contains(s1 * s2)
        assert not W_I.contains(s3)

    def test_minimal_coset_representative(self):
        """Minimal coset representative has correct length."""
        from pyw.core.bruhat import BruhatOrder

        W = WeylGroup(["A", 2])
        bruhat = BruhatOrder(W)

        W_I = bruhat.parabolic_subgroup({1})

        s1 = W.simple_reflection(1)
        s2 = W.simple_reflection(2)

        rep = W_I.minimal_coset_representative(s1 * s2)
        assert bruhat.length(rep) <= bruhat.length(s1 * s2)

    def test_left_right_coset_representatives_are_distinct(self):
        from pyw.core.bruhat import BruhatOrder

        W = WeylGroup(["A", 2])
        bruhat = BruhatOrder(W)
        W_I = bruhat.parabolic_subgroup({1})

        w = W.simple_reflection(1) * W.simple_reflection(2)
        left_rep = W_I.minimal_coset_representative(w, left=True)
        right_rep = W_I.minimal_coset_representative(w, left=False)

        assert left_rep == W.simple_reflection(2)
        assert right_rep == w

    def test_coset_representative_normalizes_input(self):
        from pyw.core.bruhat import BruhatOrder, CosetRepresentative

        W = WeylGroup(["A", 2])
        bruhat = BruhatOrder(W)
        W_I = bruhat.parabolic_subgroup({1})

        w = W.simple_reflection(1) * W.simple_reflection(2)
        coset = CosetRepresentative(w, W_I, left=False)

        assert coset.representative == w

    def test_coset_bruhat_compare_requires_same_side(self):
        from pyw.core.bruhat import BruhatOrder, CosetRepresentative

        W = WeylGroup(["A", 2])
        bruhat = BruhatOrder(W)
        W_I = bruhat.parabolic_subgroup({1})

        left_coset = CosetRepresentative(W.simple_reflection(2), W_I, left=True)
        right_coset = CosetRepresentative(W.simple_reflection(2), W_I, left=False)

        with pytest.raises(ValueError, match="different parabolic data"):
            left_coset.bruhat_le(right_coset)


class TestKazhdanLusztigPolynomials:
    """Tests for KL polynomial computation."""

    def test_P_identity(self):
        """P_{w,w} = 1 for any w."""
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W)

        e = W.one()
        s1 = W.simple_reflection(1)

        assert kl.P(e, e, at_one=True) == 1
        assert kl.P(s1, s1, at_one=True) == 1

    def test_P_adjacent(self):
        """P_{e, s_i} = 1 for simple reflections."""
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W)

        e = W.one()
        s1 = W.simple_reflection(1)

        assert kl.P(e, s1, at_one=True) == 1

    def test_Q_identity(self):
        """Q_{w,w} = 1 for any w."""
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W)

        e = W.one()
        assert kl.Q(e, e, at_one=True) == 1

    def test_Q_noncomparable_is_zero(self):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W)

        s1 = W.simple_reflection(1)
        assert kl.Q(s1, W.one(), at_one=True) == 0

    def test_Q_at_one_agrees_with_interval_inverse(self):
        from pyw.core.bruhat import BruhatOrder
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials
        from sage.all import matrix

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W)
        kl._coxeter3 = None

        bruhat = BruhatOrder(W)
        x = W.one()
        y = W.long_element()
        interval = bruhat.interval(x, y)

        p_at_one = matrix(QQ, len(interval), len(interval))
        for i, w_i in enumerate(interval):
            for j, w_j in enumerate(interval):
                if bruhat.le(w_i, w_j):
                    p_at_one[i, j] = kl.P(w_i, w_j, at_one=True)

        q_at_one = p_at_one.inverse()
        assert kl.Q(x, y, at_one=True) == q_at_one[0, len(interval) - 1]

    def test_Q_full_polynomial_falls_back_to_inversion(self):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W)
        kl._coxeter3 = None

        assert kl.Q(W.one(), W.long_element(), at_one=False) == -1

    def test_affine_bounded_interval_filters_candidates(self):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2, 1])
        kl = KazhdanLusztigPolynomials(W)

        e = W.one()
        s0 = W.simple_reflection(0)
        candidates = [e, s0, s0 * W.simple_reflection(1)]

        interval = kl.affine_bounded_interval(e, s0, candidates=candidates)

        assert interval == [e, s0]

    def test_affine_bounded_Q_matches_matrix_inversion_on_candidates(self):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2, 1])
        kl = KazhdanLusztigPolynomials(W)
        kl._coxeter3 = None

        e = W.one()
        s0 = W.simple_reflection(0)
        candidates = [e, s0]

        assert kl.affine_bounded_Q(e, s0, candidates=candidates, at_one=True) == -1

    def test_affine_bounded_Q_tilde_is_legacy_alias(self):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2, 1])
        kl = KazhdanLusztigPolynomials(W)
        kl._coxeter3 = None

        e = W.one()
        s0 = W.simple_reflection(0)
        candidates = [e, s0]

        assert kl.affine_bounded_Q_tilde(e, s0, candidates=candidates, at_one=True) == kl.affine_bounded_Q(e, s0, candidates=candidates, at_one=True)

    def test_affine_stabilizer_contains_identity_for_bounded_search(self):
        from pyw.core.affine_lie_algebra import AffineLieAlgebra
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        ala = AffineLieAlgebra(["A", 2, 1])
        W = WeylGroup(["A", 2, 1])
        kl = KazhdanLusztigPolynomials(W)

        Lambda_sage = ala.fundamental_weights_sage()
        Lambda = Lambda_sage[0]
        rho_hat = sum(Lambda_sage.values())
        candidates = [W.one(), W.simple_reflection(0)]

        stabilizer = kl.affine_stabilizer(
            Lambda,
            rho_hat=rho_hat,
            candidates=candidates,
            algebra=ala,
        )

        assert W.one() in stabilizer

    def test_affine_bounded_parabolic_Q_tilde_diagonal_is_one(self):
        from pyw.core.affine_lie_algebra import AffineLieAlgebra
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        ala = AffineLieAlgebra(["A", 2, 1])
        W = WeylGroup(["A", 2, 1])
        kl = KazhdanLusztigPolynomials(W)
        kl._coxeter3 = None

        candidates = [
            W.from_reduced_word(tuple(int(i) for i in element.word()))
            for element in ala.affine_weyl_group().elements_as_semi_direct_product(
                translation_bounds={1: (0, 0), 2: (0, 0)}
            )
        ]
        stabilizer = [W.one()]

        assert kl.affine_bounded_parabolic_Q_tilde(
            W.one(),
            W.one(),
            candidates=candidates,
            stabilizer_candidates=stabilizer,
            at_one=True,
        ) == 1

    def test_affine_bounded_parabolic_Q_tilde_noncomparable_is_zero(self):
        from pyw.core.affine_lie_algebra import AffineLieAlgebra
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        ala = AffineLieAlgebra(["A", 2, 1])
        W = WeylGroup(["A", 2, 1])
        kl = KazhdanLusztigPolynomials(W)
        kl._coxeter3 = None

        candidates = [
            W.from_reduced_word(tuple(int(i) for i in element.word()))
            for element in ala.affine_weyl_group().elements_as_semi_direct_product(
                translation_bounds={1: (0, 0), 2: (0, 0)}
            )
        ]
        stabilizer = [W.one()]
        s0 = W.simple_reflection(0)

        assert kl.affine_bounded_parabolic_Q_tilde(
            s0,
            W.one(),
            candidates=candidates,
            stabilizer_candidates=stabilizer,
            at_one=True,
        ) == 0

    def test_parabolic_Q_tilde_rejects_left_cosets(self):
        from pyw.core.bruhat import BruhatOrder, CosetRepresentative
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W)
        bruhat = BruhatOrder(W)
        W_I = bruhat.parabolic_subgroup({1})

        x = CosetRepresentative(W.one(), W_I, left=True)
        y = CosetRepresentative(W.simple_reflection(2), W_I, left=True)

        with pytest.raises(NotImplementedError, match="right cosets only"):
            kl.parabolic_Q_tilde(x, y, at_one=True)

    def test_Q_tilde_dispatches_to_coset_level_api(self):
        from pyw.core.bruhat import BruhatOrder, CosetRepresentative
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W)
        bruhat = BruhatOrder(W)
        W_I = bruhat.parabolic_subgroup({1})

        x = CosetRepresentative(W.one(), W_I, left=True)
        y = CosetRepresentative(W.simple_reflection(2), W_I, left=True)

        with pytest.raises(NotImplementedError, match="right cosets only"):
            kl.Q_tilde(x, y, at_one=True)

    def test_parabolic_Q_tilde_requires_same_parabolic(self):
        from pyw.core.bruhat import BruhatOrder, CosetRepresentative
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W)
        bruhat = BruhatOrder(W)
        W_1 = bruhat.parabolic_subgroup({1})
        W_2 = bruhat.parabolic_subgroup({2})

        x = CosetRepresentative(W.one(), W_1, left=False)
        y = CosetRepresentative(W.simple_reflection(2), W_2, left=False)

        with pytest.raises(ValueError, match="same parabolic subgroup"):
            kl.parabolic_Q_tilde(x, y, at_one=True)

    def test_parabolic_Q_tilde_rejects_infinite_groups(self):
        from pyw.core.bruhat import BruhatOrder, CosetRepresentative
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2, 1])
        kl = KazhdanLusztigPolynomials(W)
        bruhat = BruhatOrder(W)
        W_I = bruhat.parabolic_subgroup({1})

        x = CosetRepresentative(W.one(), W_I, left=False)
        y = CosetRepresentative(W.simple_reflection(0), W_I, left=False)

        with pytest.raises(ValueError, match="finite groups only"):
            kl.parabolic_Q_tilde(x, y, at_one=True)

    def test_cache_round_trip_for_Q_at_one(self, tmp_path):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W, cache_dir=tmp_path)
        value = kl.Q(W.one(), W.long_element(), at_one=True)

        cache_path = kl.save_cache()
        payload = json.loads(cache_path.read_text())

        assert payload["cache_version"] == kl.CACHE_VERSION
        assert payload["value_kind"] == "Q_at_one"

        restored = KazhdanLusztigPolynomials(W, cache_dir=tmp_path)
        assert restored.load_cache(cache_path.name)
        assert restored.Q(W.one(), W.long_element(), at_one=True) == value

    def test_cache_rejects_mismatched_cartan_type(self, tmp_path):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W_a2 = WeylGroup(["A", 2])
        W_b2 = WeylGroup(["B", 2])

        writer = KazhdanLusztigPolynomials(W_a2, cache_dir=tmp_path)
        writer.Q(W_a2.one(), W_a2.long_element(), at_one=True)
        cache_path = writer.save_cache("shared.json")

        reader = KazhdanLusztigPolynomials(W_b2, cache_dir=tmp_path)
        assert not reader.load_cache(cache_path.name)

    def test_cache_rejects_invalid_payload(self, tmp_path):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W, cache_dir=tmp_path)
        bad_path = tmp_path / "kl_cache_bad.json"
        bad_path.write_text("not valid json")

        assert not kl.load_cache(bad_path.name)

    def test_cache_rejects_wrong_value_kind(self, tmp_path):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W, cache_dir=tmp_path)
        bad_path = tmp_path / "wrong-kind.json"
        bad_path.write_text(
            json.dumps(
                {
                    "cache_version": kl.CACHE_VERSION,
                    "cartan_type": str(W.cartan_type()),
                    "value_kind": "Q_tilde_polynomial",
                    "Q_at_one_cache": {},
                }
            )
        )

        assert not kl.load_cache(bad_path.name)

    def test_cache_rejects_wrong_version(self, tmp_path):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W, cache_dir=tmp_path)
        bad_path = tmp_path / "wrong-version.json"
        bad_path.write_text(
            json.dumps(
                {
                    "cache_version": kl.CACHE_VERSION + 1,
                    "cartan_type": str(W.cartan_type()),
                    "value_kind": "Q_at_one",
                    "Q_at_one_cache": {},
                }
            )
        )

        assert not kl.load_cache(bad_path.name)

    def test_cache_rejects_legacy_dat_payload(self, tmp_path):
        from pyw.core.kazhdan_lusztig import KazhdanLusztigPolynomials

        W = WeylGroup(["A", 2])
        kl = KazhdanLusztigPolynomials(W, cache_dir=tmp_path)
        legacy_path = tmp_path / "legacy.dat"
        legacy_path.write_text(json.dumps({"old": "format"}))

        assert not kl.load_cache(legacy_path.name)


class TestFormalCharacter:
    """Tests for FormalCharacter class."""

    def test_character_addition(self):
        """Character addition works correctly."""
        from pyw.core.character import FormalCharacter

        ch1 = FormalCharacter({0: 1, 1: 2}, max_grade=5)
        ch2 = FormalCharacter({0: 1, 1: 1, 2: 1}, max_grade=5)

        result = ch1 + ch2
        assert result[0] == 2
        assert result[1] == 3
        assert result[2] == 1

    def test_character_scalar_multiplication(self):
        """Scalar multiplication works correctly."""
        from pyw.core.character import FormalCharacter

        ch = FormalCharacter({0: 1, 1: 2, 2: 3}, max_grade=5)
        result = 2 * ch

        assert result[0] == 2
        assert result[1] == 4
        assert result[2] == 6

    def test_character_shift(self):
        """Grade shift works correctly."""
        from pyw.core.character import FormalCharacter

        ch = FormalCharacter({0: 1, 1: 2}, max_grade=5)
        shifted = ch.shift(2)

        assert shifted[0] == 0
        assert shifted[2] == 1
        assert shifted[3] == 2

    def test_character_truncate(self):
        """Truncation works correctly."""
        from pyw.core.character import FormalCharacter

        ch = FormalCharacter({0: 1, 1: 2, 2: 3, 3: 4}, max_grade=10)
        truncated = ch.truncate(2)

        assert truncated[0] == 1
        assert truncated[1] == 2
        assert truncated[2] == 3
        assert truncated[3] == 0


class TestWeylKacDenominator:
    """Tests for Weyl-Kac denominator."""

    def test_inverse_denominator_leading_term(self):
        """Inverse denominator has leading coefficient 1."""
        from pyw.core.character import WeylKacDenominator
        from pyw.core.affine_lie_algebra import AffineLieAlgebra

        ala = AffineLieAlgebra(["A", 2, 1])
        denom = WeylKacDenominator(ala)

        inv = denom.inverse(max_grade=5)
        assert inv[0] == 1


class TestVermaCharacter:
    """Tests for Verma module character."""

    def test_verma_character_exists(self):
        """Verma character can be computed."""
        from pyw.core.character import VermaCharacter
        from pyw.core.affine_lie_algebra import AffineLieAlgebra
        from pyw.core.affine_weight import AffineWeight

        ala = AffineLieAlgebra(["A", 2, 1])
        Lambda = AffineWeight.affine_fundamental_weight(ala, 1)

        verma = VermaCharacter(ala, Lambda)
        ch = verma.character(max_grade=3)

        assert ch[0] != 0

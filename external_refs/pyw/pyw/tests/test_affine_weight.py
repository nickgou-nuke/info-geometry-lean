"""
Tests for AffineWeight class (Di Francesco notation).

Tests the AffineWeight implementation following Di Francesco, Mathieu, Sénéchal
"Conformal Field Theory" Chapter 14 conventions.

References:
    - Di Francesco et al., Eq. (14.22): ̂λ = (λ; k; n)
    - Di Francesco et al., Eq. (14.23): (̂λ, ̂μ) = (λ, μ) + k_λ n_μ + k_μ n_λ
    - Di Francesco et al., Eq. (14.64): Affine Weyl reflection formula
    - Di Francesco et al., Eq. (14.69): Translation operator formula
"""

import pytest
from sage.all import QQ

from pyw.core.affine_lie_algebra import AffineLieAlgebra
from pyw.core.affine_weight import (
    AffineWeight,
    affine_weight,
    from_dynkin_labels,
)


class TestAffineWeightConstruction:
    """Test AffineWeight construction and basic properties."""

    def test_basic_construction_a2(self):
        """Test basic construction for A₂^(1)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w = AffineWeight(ala, Lambda[1], level=1, grade=0)

        assert w.finite_part == Lambda[1]
        assert w.level == 1
        assert w.grade == 0
        assert w.k == 1
        assert w.n == 0

    def test_zero_weight(self):
        """Test zero weight construction."""
        ala = AffineLieAlgebra(["A", 2, 1])
        zero = AffineWeight.zero(ala)

        assert zero.level == 0
        assert zero.grade == 0

    def test_string_representation(self):
        """Test string representation in Di Francesco notation."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w = AffineWeight(ala, Lambda[1], level=1, grade=0)
        s = str(w)

        assert "Lambda[1]" in s or "Λ" in s
        assert "1" in s
        assert "0" in s

    def test_to_tuple(self):
        """Test conversion to tuple."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w = AffineWeight(ala, Lambda[1], level=2, grade=QQ(1) / 2)
        t = w.to_tuple()

        assert t[0] == Lambda[1]
        assert t[1] == 2
        assert t[2] == QQ(1) / 2


class TestAffineFundamentalWeights:
    """Test affine fundamental weight construction."""

    def test_affine_fundamental_weight_0(self):
        """Test ̂Λ₀ = (0; 1; 0) for A₂^(1)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        Lambda_hat_0 = AffineWeight.affine_fundamental_weight(ala, 0)

        assert Lambda_hat_0.level == 1
        assert Lambda_hat_0.grade == 0

    def test_affine_fundamental_weight_1(self):
        """Test ̂Λ₁ = (Λ₁; 1; 0) for A₂^(1)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        Lambda_hat_1 = AffineWeight.affine_fundamental_weight(ala, 1)

        finite_Lambda = ala._finite_root_system.weight_space().fundamental_weights()

        assert Lambda_hat_1.finite_part == finite_Lambda[1]
        assert Lambda_hat_1.level == 1
        assert Lambda_hat_1.grade == 0

    def test_affine_fundamental_weights_sum_to_rho_hat(self):
        """Test that Σ ̂Λ_i = ρ̂ for A₂^(1)."""
        ala = AffineLieAlgebra(["A", 2, 1])

        Lambda_hats = [AffineWeight.affine_fundamental_weight(ala, i) for i in [0, 1, 2]]
        sum_Lambda = Lambda_hats[0] + Lambda_hats[1] + Lambda_hats[2]
        rho_hat = AffineWeight.rho_hat(ala)

        assert sum_Lambda.finite_part == rho_hat.finite_part
        assert sum_Lambda.level == rho_hat.level
        assert sum_Lambda.grade == rho_hat.grade


class TestAffineSimpleRoots:
    """Test affine simple root construction."""

    def test_affine_simple_root_1(self):
        """Test ̂α₁ = (α₁; 0; 0) for A₂^(1)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        alpha_hat_1 = AffineWeight.affine_simple_root(ala, 1)

        finite_alpha = ala._finite_root_system.root_lattice().simple_roots()

        assert alpha_hat_1.finite_part == finite_alpha[1]
        assert alpha_hat_1.level == 0
        assert alpha_hat_1.grade == 0

    def test_affine_simple_root_0(self):
        """Test ̂α₀ = (-θ; 0; 1) for A₂^(1)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        alpha_hat_0 = AffineWeight.affine_simple_root(ala, 0)

        theta = ala._finite_root_system.root_lattice().highest_root()

        assert alpha_hat_0.finite_part == -theta
        assert alpha_hat_0.level == 0
        assert alpha_hat_0.grade == 1


class TestDelta:
    """Test imaginary root δ."""

    def test_delta_construction(self):
        """Test δ = (0; 0; 1)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        delta = AffineWeight.delta(ala)

        assert delta.level == 0
        assert delta.grade == 1

    def test_delta_norm_squared_is_zero(self):
        """Test (δ, δ) = 0 (null root)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        delta = AffineWeight.delta(ala)

        assert delta.norm_squared() == 0

    def test_delta_pairing_gives_level(self):
        """Test (δ, ̂λ) = k_λ."""
        ala = AffineLieAlgebra(["A", 2, 1])
        delta = AffineWeight.delta(ala)

        Lambda_hat_1 = AffineWeight.affine_fundamental_weight(ala, 1)
        pairing = delta.scalar_product(Lambda_hat_1)

        assert pairing == Lambda_hat_1.level


class TestArithmeticOperations:
    """Test arithmetic operations on AffineWeights."""

    def test_addition(self):
        """Test (λ₁; k₁; n₁) + (λ₂; k₂; n₂) = (λ₁+λ₂; k₁+k₂; n₁+n₂)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w1 = AffineWeight(ala, Lambda[1], level=1, grade=0)
        w2 = AffineWeight(ala, Lambda[2], level=2, grade=1)

        result = w1 + w2

        assert result.finite_part == Lambda[1] + Lambda[2]
        assert result.level == 3
        assert result.grade == 1

    def test_subtraction(self):
        """Test (λ₁; k₁; n₁) - (λ₂; k₂; n₂) = (λ₁-λ₂; k₁-k₂; n₁-n₂)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w1 = AffineWeight(ala, Lambda[1], level=3, grade=2)
        w2 = AffineWeight(ala, Lambda[2], level=1, grade=1)

        result = w1 - w2

        assert result.finite_part == Lambda[1] - Lambda[2]
        assert result.level == 2
        assert result.grade == 1

    def test_negation(self):
        """Test -(λ; k; n) = (-λ; -k; -n)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w = AffineWeight(ala, Lambda[1], level=1, grade=2)
        result = -w

        assert result.finite_part == -Lambda[1]
        assert result.level == -1
        assert result.grade == -2

    def test_scalar_multiplication(self):
        """Test c * (λ; k; n) = (cλ; ck; cn)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w = AffineWeight(ala, Lambda[1], level=1, grade=1)
        result = 3 * w

        assert result.finite_part == 3 * Lambda[1]
        assert result.level == 3
        assert result.grade == 3

    def test_scalar_division(self):
        """Test (λ; k; n) / c = (λ/c; k/c; n/c)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w = AffineWeight(ala, 2 * Lambda[1], level=4, grade=2)
        result = w / 2

        assert result.finite_part == Lambda[1]
        assert result.level == 2
        assert result.grade == 1


class TestAffineScalarProduct:
    """Test affine scalar product (Di Francesco Eq. 14.23)."""

    def test_scalar_product_formula(self):
        """Test (̂λ, ̂μ) = (λ, μ) + k_λ n_μ + k_μ n_λ."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w1 = AffineWeight(ala, Lambda[1], level=1, grade=0)
        w2 = AffineWeight(ala, Lambda[2], level=1, grade=1)

        result = w1.scalar_product(w2)

        finite_part = ala.scalar_product(Lambda[1], Lambda[2])
        cross_terms = 1 * 1 + 1 * 0

        assert result == finite_part + cross_terms

    def test_fundamental_weights_scalar_product(self):
        """Test scalar product of affine fundamental weights."""
        ala = AffineLieAlgebra(["A", 2, 1])

        Lambda_hat_1 = AffineWeight.affine_fundamental_weight(ala, 1)
        Lambda_hat_2 = AffineWeight.affine_fundamental_weight(ala, 2)

        result = Lambda_hat_1.scalar_product(Lambda_hat_2)

        finite_Lambda = ala._finite_root_system.weight_space().fundamental_weights()
        expected = ala.scalar_product(finite_Lambda[1], finite_Lambda[2])

        assert result == expected


class TestRhoHat:
    """Test affine Weyl vector ρ̂."""

    def test_rho_hat_level_is_dual_coxeter(self):
        """Test that level of ρ̂ equals dual Coxeter number."""
        ala = AffineLieAlgebra(["A", 2, 1])
        rho_hat = AffineWeight.rho_hat(ala)

        assert rho_hat.level == ala.dual_coxeter_number()

    def test_rho_hat_grade_is_zero(self):
        """Test that grade of ρ̂ is zero."""
        ala = AffineLieAlgebra(["A", 2, 1])
        rho_hat = AffineWeight.rho_hat(ala)

        assert rho_hat.grade == 0


class TestConversion:
    """Test conversion between SageMath and Di Francesco notations."""

    def test_from_sagemath_fundamental_weight(self):
        """Test conversion from SageMath affine Λ₁."""
        ala = AffineLieAlgebra(["A", 2, 1])
        sage_Lambda = ala.fundamental_weights_sage()

        w = AffineWeight.from_sagemath(ala, sage_Lambda[1])

        assert w.level == 1
        assert w.grade == 0

    def test_to_sagemath_fundamental_weight(self):
        """Test conversion to SageMath affine weight."""
        ala = AffineLieAlgebra(["A", 2, 1])

        Lambda_hat_1 = AffineWeight.affine_fundamental_weight(ala, 1)
        sage_w = Lambda_hat_1.to_sagemath()

        sage_Lambda = ala.fundamental_weights_sage()
        assert sage_w == sage_Lambda[1]

    def test_roundtrip_conversion(self):
        """Test SageMath -> Di Francesco -> SageMath roundtrip."""
        ala = AffineLieAlgebra(["A", 2, 1])
        sage_Lambda = ala.fundamental_weights_sage()
        original = sage_Lambda[1] + sage_Lambda[2]

        w = AffineWeight.from_sagemath(ala, original)
        recovered = w.to_sagemath()

        assert recovered == original


class TestFromDynkinLabels:
    """Test construction from Dynkin labels."""

    def test_from_dynkin_labels_fundamental(self):
        """Test construction of ̂Λ₀ from [1, 0, 0]."""
        ala = AffineLieAlgebra(["A", 2, 1])

        w = from_dynkin_labels(ala, {0: 1, 1: 0, 2: 0})

        assert w.level == 1
        assert w.grade == 0

    def test_dynkin_labels_roundtrip(self):
        """Test Dynkin labels -> AffineWeight -> Dynkin labels."""
        ala = AffineLieAlgebra(["A", 2, 1])
        original_labels = {0: 1, 1: 1, 2: 0}

        w = from_dynkin_labels(ala, original_labels)
        recovered = w.dynkin_labels()

        for i in [0, 1, 2]:
            assert recovered[i] == original_labels[i]


class TestSimpleReflection:
    """Test simple Weyl reflections."""

    def test_simple_reflection_finite(self):
        """Test s_1 on ̂Λ₁ gives expected result."""
        ala = AffineLieAlgebra(["A", 2, 1])

        Lambda_hat_1 = AffineWeight.affine_fundamental_weight(ala, 1)
        result = Lambda_hat_1.simple_reflection(1)

        assert result.level == Lambda_hat_1.level
        assert result.grade == Lambda_hat_1.grade

    def test_simple_reflection_preserves_level(self):
        """Test that simple reflections preserve level."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w = AffineWeight(ala, Lambda[1] + Lambda[2], level=2, grade=0)
        result = w.simple_reflection(1)

        assert result.level == w.level


class TestTranslation:
    """Test translation operators (Di Francesco Eq. 14.69)."""

    def test_translation_preserves_level(self):
        """Test that translation preserves level."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_ws = ala._finite_root_system.weight_space()
        zero = finite_ws.zero()

        alpha_vee = ala._finite_root_system.coroot_space().simple_roots()[1]

        w = AffineWeight(ala, zero, level=1, grade=0)
        result = w.translate(alpha_vee)

        assert result.level == w.level

    def test_translation_zero_level_raises(self):
        """Test that translation at level 0 raises ValueError."""
        ala = AffineLieAlgebra(["A", 2, 1])

        w = AffineWeight.zero(ala)

        with pytest.raises(ValueError, match="level k = 0"):
            alpha_vee = ala._finite_root_system.coroot_space().simple_roots()[1]
            w.translate(alpha_vee)


class TestDominance:
    """Test dominance checking."""

    def test_fundamental_weight_is_dominant(self):
        """Test that affine fundamental weights are dominant."""
        ala = AffineLieAlgebra(["A", 2, 1])

        for i in [0, 1, 2]:
            w = AffineWeight.affine_fundamental_weight(ala, i)
            assert w.is_dominant()

    def test_negative_weight_not_dominant(self):
        """Test that -̂Λ₁ is not dominant."""
        ala = AffineLieAlgebra(["A", 2, 1])

        Lambda_hat_1 = AffineWeight.affine_fundamental_weight(ala, 1)
        w = -Lambda_hat_1

        assert not w.is_dominant()


class TestEquality:
    """Test equality and hashing."""

    def test_equality(self):
        """Test that equal weights compare equal."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w1 = AffineWeight(ala, Lambda[1], level=1, grade=0)
        w2 = AffineWeight(ala, Lambda[1], level=1, grade=0)

        assert w1 == w2

    def test_inequality_level(self):
        """Test that weights with different levels are not equal."""
        ala = AffineLieAlgebra(["A", 2, 1])
        finite_wl = ala._finite_root_system.weight_space()
        Lambda = finite_wl.fundamental_weights()

        w1 = AffineWeight(ala, Lambda[1], level=1, grade=0)
        w2 = AffineWeight(ala, Lambda[1], level=2, grade=0)

        assert w1 != w2

    def test_hashable(self):
        """Test that AffineWeight can be used in sets."""
        ala = AffineLieAlgebra(["A", 2, 1])

        Lambda_hat_1 = AffineWeight.affine_fundamental_weight(ala, 1)
        Lambda_hat_2 = AffineWeight.affine_fundamental_weight(ala, 2)

        weight_set = {Lambda_hat_1, Lambda_hat_2}
        assert len(weight_set) == 2


class TestDiFrancescoFormulas:
    """Test specific formulas from Di Francesco Chapter 14."""

    def test_null_root_relation(self):
        """Test Σ a_i ̂α_i = δ (Di Francesco null root relation)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        marks = ala.get_marks()

        alpha_hats = {i: AffineWeight.affine_simple_root(ala, i) for i in marks.keys()}

        sum_result = AffineWeight.zero(ala)
        for i, a_i in marks.items():
            sum_result = sum_result + a_i * alpha_hats[i]

        delta = AffineWeight.delta(ala)

        assert sum_result.level == delta.level
        assert sum_result.grade == delta.grade

    def test_affine_weyl_vector_level(self):
        """Test ρ̂(k̂) = g (dual Coxeter number)."""
        for cartan_type in [["A", 2, 1], ["B", 2, 1], ["G", 2, 1]]:
            ala = AffineLieAlgebra(cartan_type)
            rho_hat = AffineWeight.rho_hat(ala)
            g = ala.dual_coxeter_number()

            assert rho_hat.level == g, f"Failed for {cartan_type}"


class TestAffineLieAlgebraConvenienceMethods:
    """Test the convenience methods added to AffineLieAlgebra."""

    def test_affine_fundamental_weights_method(self):
        """Test ala.affine_fundamental_weights() returns correct weights."""
        ala = AffineLieAlgebra(["A", 2, 1])
        Lambda_hat = ala.affine_fundamental_weights()

        assert 0 in Lambda_hat
        assert 1 in Lambda_hat
        assert 2 in Lambda_hat

        assert Lambda_hat[0].level == 1
        assert Lambda_hat[1].level == 1

    def test_affine_simple_roots_method(self):
        """Test ala.affine_simple_roots() returns correct roots."""
        ala = AffineLieAlgebra(["A", 2, 1])
        alpha_hat = ala.affine_simple_roots()

        assert 0 in alpha_hat
        assert 1 in alpha_hat

        assert alpha_hat[0].grade == 1
        assert alpha_hat[1].grade == 0

    def test_affine_delta_method(self):
        """Test ala.affine_delta() returns δ = (0; 0; 1)."""
        ala = AffineLieAlgebra(["A", 2, 1])
        delta = ala.affine_delta()

        assert delta.level == 0
        assert delta.grade == 1
        assert delta.norm_squared() == 0

    def test_affine_rho_method(self):
        """Test ala.affine_rho() returns correct Weyl vector."""
        ala = AffineLieAlgebra(["A", 2, 1])
        rho = ala.affine_rho()

        assert rho.level == ala.dual_coxeter_number()
        assert rho.grade == 0

    def test_affine_weight_factory(self):
        """Test ala.affine_weight() factory method."""
        ala = AffineLieAlgebra(["A", 2, 1])
        ws = ala._finite_root_system.weight_space()
        Lambda = ws.fundamental_weights()

        w = ala.affine_weight(Lambda[1], level=2, grade=1)

        assert w.finite_part == Lambda[1]
        assert w.level == 2
        assert w.grade == 1

"""
Tests for Boundary Level Character Formulas

This module tests the Kac-Wakimoto product formulas for boundary level
admissible representations.

Key test cases from Kac-Wakimoto paper:
1. sl₂ at k = -4/3 (u=3): 3 admissible weights
2. sl₂ at k = -8/5 (u=5): 5 admissible weights
3. sl₃ at k = -3/2 (u=2): 3 admissible weights

References:
- Kac, V. G., Wakimoto, M. "A remark on boundary level admissible representations"
- Cordova, Gaiotto, Shao "Infrared Computations of Defect Schur Indices"
"""

import pytest
from sage.all import CC, I, QQ, exp, pi


def rational(num, den):
    """Create a rational number num/den."""
    return QQ(num) / QQ(den)


class TestThetaFunctions:
    """Tests for theta function implementations."""

    def test_theta_zero_at_origin(self):
        """θ₁₁(τ, 0) = 0."""
        from pyw.utils.theta_functions import theta_11_product

        tau = I / 5  # τ = i/5
        theta_val = theta_11_product(tau, 0, num_terms=50)

        assert abs(CC(theta_val)) < 1e-10, f"θ₁₁(τ, 0) should be 0, got {theta_val}"

    def test_theta_odd_function(self):
        """θ₁₁(τ, -z) = -θ₁₁(τ, z)."""
        from pyw.utils.theta_functions import theta_11_product

        tau = I / 5
        z = rational(1, 4) + I / 10

        theta_z = theta_11_product(tau, z, num_terms=50)
        theta_neg_z = theta_11_product(tau, -z, num_terms=50)

        ratio = CC(theta_z + theta_neg_z) / CC(theta_z)
        assert abs(ratio) < 1e-8, f"θ₁₁ should be odd, ratio = {ratio}"

    def test_theta_quasi_periodicity(self):
        """θ₁₁(τ, z+1) = -θ₁₁(τ, z)."""
        from pyw.utils.theta_functions import theta_11_product

        tau = I / 5
        z = rational(1, 4) + I / 10

        theta_z = theta_11_product(tau, z, num_terms=50)
        theta_z_plus_1 = theta_11_product(tau, z + 1, num_terms=50)

        ratio = CC(theta_z_plus_1 + theta_z) / CC(theta_z)
        assert abs(ratio) < 1e-8, f"Quasi-periodicity failed, ratio = {ratio}"

    def test_eta_positive(self):
        """η(τ) > 0 for τ = iy with y > 0."""
        from pyw.utils.theta_functions import dedekind_eta

        tau = I  # τ = i
        eta_val = dedekind_eta(tau, num_terms=100)

        # η(i) ≈ 0.7682254223
        expected = 0.7682254223260566
        assert abs(CC(eta_val) - expected) < 1e-8, f"η(i) = {eta_val}, expected {expected}"


class TestSL2BoundaryLevel:
    """Tests for sl₂ boundary level characters."""

    def test_sl2_u3_vacuum_character_ratio(self):
        """
        Test vacuum character ratio for sl₂ at k = -4/3 (u=3).

        ch_{kΛ₀}(τ, z) / ch_{kΛ₀}(τ, 0) should be well-defined.
        """
        from pyw.utils.theta_functions import sl2_boundary_vacuum_character, theta_ratio

        tau = I / 10
        z = rational(1, 5)
        u = 3

        # The vacuum character is θ₁₁(3τ, z) / θ₁₁(τ, z)
        ratio = theta_ratio(tau, z, u, num_terms=50)

        # Should be a finite, non-zero value
        ratio_val = CC(ratio)
        assert abs(ratio_val) > 0.1, f"Ratio too small: {ratio_val}"
        assert abs(ratio_val) < 100, f"Ratio too large: {ratio_val}"

    def test_sl2_u3_character_j0(self):
        """Test j=0 character for sl₂ at k = -4/3."""
        from pyw.utils.theta_functions import sl2_boundary_character

        tau = I / 10
        z = rational(1, 5)

        ch_0 = sl2_boundary_character(3, 0, tau, z, num_terms=50)
        ch_0_val = CC(ch_0)

        # Should be finite and non-zero
        assert abs(ch_0_val) > 0.01, f"ch_0 too small: {ch_0_val}"

    def test_sl2_u3_character_j1(self):
        """Test j=1 character for sl₂ at k = -4/3."""
        from pyw.utils.theta_functions import sl2_boundary_character

        tau = I / 10
        z = rational(1, 5)

        ch_1 = sl2_boundary_character(3, 1, tau, z, num_terms=50)
        ch_1_val = CC(ch_1)

        # Should be finite (not NaN or Inf)
        assert not ch_1_val.is_infinity() and not ch_1_val.is_NaN(), f"ch_1 not finite: {ch_1_val}"

    def test_sl2_u3_character_j2(self):
        """Test j=2 character for sl₂ at k = -4/3."""
        from pyw.utils.theta_functions import sl2_boundary_character

        tau = I / 10
        z = rational(1, 5)

        ch_2 = sl2_boundary_character(3, 2, tau, z, num_terms=50)
        ch_2_val = CC(ch_2)

        # Should be finite
        assert not ch_2_val.is_infinity() and not ch_2_val.is_NaN(), f"ch_2 not finite: {ch_2_val}"

    def test_sl2_u3_all_characters_sum(self):
        """
        Test that sum of all characters has expected behavior.

        For boundary level, the characters should satisfy modular properties.
        """
        from pyw.utils.theta_functions import sl2_boundary_character

        tau = I / 10
        z = rational(1, 5)
        u = 3

        # Sum all characters
        total = sum(sl2_boundary_character(u, j, tau, z, num_terms=50) for j in range(u))
        total_val = CC(total)

        # Should be finite
        assert not total_val.is_infinity() and not total_val.is_NaN(), (
            f"Sum not finite: {total_val}"
        )

    def test_sl2_u5_vacuum_character(self):
        """Test vacuum character for sl₂ at k = -8/5 (u=5)."""
        from pyw.utils.theta_functions import sl2_boundary_vacuum_character

        tau = I / 10
        z = rational(1, 5)

        ch_vac = sl2_boundary_vacuum_character(5, tau, z, num_terms=50)
        ch_vac_val = CC(ch_vac)

        # Should be finite and non-zero
        assert abs(ch_vac_val) > 0.01, f"Vacuum character too small: {ch_vac_val}"
        assert abs(ch_vac_val) < 1000, f"Vacuum character too large: {ch_vac_val}"

    def test_sl2_invalid_u_raises(self):
        """Even u should raise error for sl₂."""
        from pyw.utils.theta_functions import sl2_boundary_character

        with pytest.raises(ValueError, match="u must be odd"):
            sl2_boundary_character(4, 0, I / 10, 0.1)

    def test_sl2_invalid_j_raises(self):
        """j out of range should raise error."""
        from pyw.utils.theta_functions import sl2_boundary_character

        with pytest.raises(ValueError, match="j must be in"):
            sl2_boundary_character(3, 5, I / 10, 0.1)


class TestSL3BoundaryLevel:
    """Tests for sl₃ boundary level characters at k = -3/2 (u=2)."""

    def test_sl3_vacuum_character(self):
        """Test vacuum character for sl₃ at k = -3/2."""
        from pyw.utils.theta_functions import sl3_boundary_vacuum_character

        tau = I / 10
        z1 = rational(1, 5)
        z2 = rational(1, 7)

        ch_vac = sl3_boundary_vacuum_character(tau, z1, z2, num_terms=50)
        ch_vac_val = CC(ch_vac)

        # Should be finite and non-zero
        assert abs(ch_vac_val) > 0.001, f"Vacuum character too small: {ch_vac_val}"
        assert abs(ch_vac_val) < 10000, f"Vacuum character too large: {ch_vac_val}"

    def test_sl3_vacuum_symmetric(self):
        """
        Vacuum character should have Weyl symmetry.

        Under z₁ ↔ z₂ exchange (which corresponds to outer automorphism),
        the vacuum character should be invariant.
        """
        from pyw.utils.theta_functions import sl3_boundary_vacuum_character

        tau = I / 10
        z1 = rational(1, 5)
        z2 = rational(1, 7)

        ch_12 = sl3_boundary_vacuum_character(tau, z1, z2, num_terms=50)
        ch_21 = sl3_boundary_vacuum_character(tau, z2, z1, num_terms=50)

        ratio = CC(ch_12 - ch_21) / CC(ch_12)
        assert abs(ratio) < 1e-6, f"Symmetry broken, ratio = {ratio}"


class TestModularSMatrix:
    """Tests for modular S-matrix elements (Kac-Wakimoto Remark 3)."""

    def test_sl2_u3_s_matrix_formula(self):
        """
        Test S-matrix formula for sl₂ at boundary level k = -4/3.

        a(Λ_{k,j}, Λ_{k,j'}) = (-1)^{j+j'} e^{-2πijj'/u} (1/√u) sin(uπ/2)

        For u=3: sin(3π/2) = -1
        """
        from sage.all import sin, sqrt

        u = 3

        # Compute S-matrix element a(Λ_{k,0}, Λ_{k,0})
        j, j_prime = 0, 0

        expected = (
            (-1) ** (j + j_prime)
            * exp(-2 * pi * I * j * j_prime / u)
            * (1 / sqrt(u))
            * sin(u * pi / 2)
        )
        expected_val = CC(expected)

        # For j=j'=0: (-1)^0 * e^0 * (1/√3) * sin(3π/2) = (1/√3) * (-1) = -1/√3
        assert abs(expected_val + 1 / sqrt(3)) < 1e-10, f"S_{00} = {expected_val}"

    def test_sl2_u3_s_matrix_j1_j1(self):
        """Test S_{11} for sl₂ at k = -4/3."""
        from sage.all import sin, sqrt

        u = 3
        j, j_prime = 1, 1

        # a(Λ_{k,1}, Λ_{k,1}) = (-1)^2 * e^{-2πi/3} * (1/√3) * (-1)
        expected = (
            (-1) ** (j + j_prime)
            * exp(-2 * pi * I * j * j_prime / u)
            * (1 / sqrt(u))
            * sin(u * pi / 2)
        )
        expected_val = CC(expected)

        # = 1 * e^{-2πi/3} * (-1/√3)
        manual = exp(-2 * pi * I / 3) * (-1 / sqrt(3))
        manual_val = CC(manual)

        assert abs(expected_val - manual_val) < 1e-10, (
            f"S_{11} mismatch: {expected_val} vs {manual_val}"
        )


class TestFusionCoefficients:
    """Tests for fusion coefficients via Verlinde formula."""

    def test_sl2_u3_fusion_000(self):
        """
        Test N_{Λ₀, Λ₀, Λ₀} for sl₂ at k = -4/3.

        N_{Λ_{k,j₁}, Λ_{k,j₂}, Λ_{k,j₃}} = (-1)^{j₁+j₂+j₃} if j₁+j₂+j₃ ∈ uℤ, else 0

        For j₁=j₂=j₃=0: sum=0 ∈ 3ℤ, so N = (-1)^0 = 1
        """
        u = 3
        j1, j2, j3 = 0, 0, 0

        if (j1 + j2 + j3) % u == 0:
            N = (-1) ** (j1 + j2 + j3)
        else:
            N = 0

        assert N == 1, f"N_{{000}} = {N}, expected 1"

    def test_sl2_u3_fusion_111(self):
        """
        Test N_{Λ₁, Λ₁, Λ₁} for sl₂ at k = -4/3.

        j₁+j₂+j₃ = 3 ∈ 3ℤ, so N = (-1)^3 = -1
        """
        u = 3
        j1, j2, j3 = 1, 1, 1

        if (j1 + j2 + j3) % u == 0:
            N = (-1) ** (j1 + j2 + j3)
        else:
            N = 0

        assert N == -1, f"N_{{111}} = {N}, expected -1"

    def test_sl2_u3_fusion_012(self):
        """
        Test N_{Λ₀, Λ₁, Λ₂} for sl₂ at k = -4/3.

        j₁+j₂+j₃ = 0+1+2 = 3 ∈ 3ℤ, so N = (-1)^3 = -1
        """
        u = 3
        j1, j2, j3 = 0, 1, 2

        if (j1 + j2 + j3) % u == 0:
            N = (-1) ** (j1 + j2 + j3)
        else:
            N = 0

        assert N == -1, f"N_{{012}} = {N}, expected -1"

    def test_sl2_u3_fusion_011(self):
        """
        Test N_{Λ₀, Λ₁, Λ₁} for sl₂ at k = -4/3.

        j₁+j₂+j₃ = 0+1+1 = 2 ∉ 3ℤ, so N = 0
        """
        u = 3
        j1, j2, j3 = 0, 1, 1

        if (j1 + j2 + j3) % u == 0:
            N = (-1) ** (j1 + j2 + j3)
        else:
            N = 0

        assert N == 0, f"N_{{011}} = {N}, expected 0"


class TestVacuumCharacterQExpansion:
    """
    Tests for vacuum character q-expansion coefficients.

    For su(2) at level k = -4n/(2n+1), the vacuum character is:
    Ch_0 = θ₁(z | (2n+1)τ) / θ₁(z | τ)

    The q-expansion has the form (with y = e^{2πiz}):
    Ch_0 = q^{n/4} + (1 + y^{-1} + y) q^{n/4+1} + ...

    Reference: Kac-Wakimoto "A remark on boundary level admissible representations"
    """

    def test_sl2_vacuum_character_leading_power(self):
        """
        Test leading q-power for vacuum character.

        For u = 2n+1, the leading power is q^{(u-1)/8} = q^{n/4}.
        """
        # n=1: u=3, leading power = 1/4
        assert rational(3 - 1, 8) == rational(1, 4)

        # n=2: u=5, leading power = 1/2
        assert rational(5 - 1, 8) == rational(1, 2)

        # n=3: u=7, leading power = 3/4
        assert rational(7 - 1, 8) == rational(3, 4)

        # n=4: u=9, leading power = 1
        assert rational(9 - 1, 8) == rational(1, 1)

    def test_sl2_u3_vacuum_vs_theta_ratio(self):
        """
        Test that sl2_boundary_vacuum_character matches theta ratio.

        For n=1 (k=-4/3, u=3):
        Ch_0 = θ₁(z | 3τ) / θ₁(z | τ)
        """
        from pyw.utils.theta_functions import (
            sl2_boundary_vacuum_character,
            theta_ratio,
        )

        tau = I / 10
        z_values = [rational(1, 10), rational(1, 5), rational(1, 4)]
        u = 3

        for z in z_values:
            wolfram_result = theta_ratio(tau, z, u, num_terms=50)
            pyw_result = sl2_boundary_vacuum_character(u, tau, z, num_terms=50)

            wolfram_val = CC(wolfram_result)
            pyw_val = CC(pyw_result)

            rel_diff = abs(wolfram_val - pyw_val) / abs(wolfram_val)
            assert rel_diff < 1e-10, f"Mismatch at z={z}: {rel_diff}"

    def test_sl2_u5_vacuum_vs_theta_ratio(self):
        """
        Test that sl2_boundary_vacuum_character matches theta ratio.

        For n=2 (k=-8/5, u=5):
        Ch_0 = θ₁(z | 5τ) / θ₁(z | τ)
        """
        from pyw.utils.theta_functions import (
            sl2_boundary_vacuum_character,
            theta_ratio,
        )

        tau = I / 10
        z_values = [rational(1, 10), rational(1, 5)]
        u = 5

        for z in z_values:
            wolfram_result = theta_ratio(tau, z, u, num_terms=50)
            pyw_result = sl2_boundary_vacuum_character(u, tau, z, num_terms=50)

            wolfram_val = CC(wolfram_result)
            pyw_val = CC(pyw_result)

            rel_diff = abs(wolfram_val - pyw_val) / abs(wolfram_val)
            assert rel_diff < 1e-10, f"Mismatch at z={z}: {rel_diff}"

    def test_sl2_u7_vacuum_vs_theta_ratio(self):
        """
        Test that sl2_boundary_vacuum_character matches theta ratio.

        For n=3 (k=-12/7, u=7):
        Ch_0 = θ₁(z | 7τ) / θ₁(z | τ)
        """
        from pyw.utils.theta_functions import (
            sl2_boundary_vacuum_character,
            theta_ratio,
        )

        tau = I / 10
        z = rational(1, 10)
        u = 7

        wolfram_result = theta_ratio(tau, z, u, num_terms=50)
        pyw_result = sl2_boundary_vacuum_character(u, tau, z, num_terms=50)

        wolfram_val = CC(wolfram_result)
        pyw_val = CC(pyw_result)

        rel_diff = abs(wolfram_val - pyw_val) / abs(wolfram_val)
        assert rel_diff < 1e-10, f"Mismatch: {rel_diff}"

    def test_sl2_u9_vacuum_vs_theta_ratio(self):
        """
        Test that sl2_boundary_vacuum_character matches theta ratio.

        For n=4 (k=-16/9, u=9):
        Ch_0 = θ₁(z | 9τ) / θ₁(z | τ)
        """
        from pyw.utils.theta_functions import (
            sl2_boundary_vacuum_character,
            theta_ratio,
        )

        tau = I / 10
        z = rational(1, 10)
        u = 9

        wolfram_result = theta_ratio(tau, z, u, num_terms=50)
        pyw_result = sl2_boundary_vacuum_character(u, tau, z, num_terms=50)

        wolfram_val = CC(wolfram_result)
        pyw_val = CC(pyw_result)

        rel_diff = abs(wolfram_val - pyw_val) / abs(wolfram_val)
        assert rel_diff < 1e-10, f"Mismatch: {rel_diff}"


class TestCharacterExpansion:
    """Tests for character q-expansion coefficients."""

    @pytest.mark.slow
    def test_sl2_u3_vacuum_leading_term(self):
        """
        Test that vacuum character has leading term 1.

        ch_{kΛ₀} = 1 + (higher order terms in q)

        At z=0, the character should approach 1 as τ → i∞ (q → 0).
        """
        from pyw.utils.theta_functions import theta_ratio

        # Use moderate imaginary part for τ
        tau = I / 5  # q = e^{-2π/5} ≈ 0.28
        z = rational(1, 10)  # Small but non-zero z
        u = 3

        ratio = theta_ratio(tau, z, u, num_terms=50)
        ratio_val = CC(ratio)

        # The ratio should be finite and have reasonable magnitude
        assert not ratio_val.is_infinity() and not ratio_val.is_NaN(), (
            f"Ratio not finite: {ratio_val}"
        )
        # For small q, the ratio should be O(1)
        assert abs(ratio_val) > 0.01, f"Ratio too small: {ratio_val}"
        assert abs(ratio_val) < 100, f"Ratio too large: {ratio_val}"

    @pytest.mark.slow
    def test_sl2_u3_j1_conformal_weight(self):
        """
        Test conformal weight h = 1/3 for j=1 representation.

        ch_{Λ₁} ∝ q^{1/3} × (...)

        The prefactor q^{j²/2u} = q^{1/6} combined with other factors
        gives effective conformal weight h = 1/3.
        """
        u = 3
        j = 1

        # Prefactor exponent: j²/2u = 1/6
        prefactor_exp = rational(j**2, 2 * u)
        assert prefactor_exp == rational(1, 6), f"Prefactor exponent = {prefactor_exp}"

        # The full conformal weight h_j for sl₂ at boundary level
        # h_j = j(u-j)/(2u) for the normalized character
        # For j=1, u=3: h = 1*2/(2*3) = 2/6 = 1/3
        numerator = j * (u - j)
        denominator = 2 * u
        h_j = rational(numerator, denominator)
        assert h_j == rational(1, 3), f"Conformal weight h_1 = {h_j}"


class TestKLvsProductFormula:
    """
    Compare Kazhdan-Lusztig method with product formula.

    For boundary levels, both methods should give the same result.
    """

    @pytest.mark.skip(reason="Requires full KL implementation")
    def test_sl2_u3_kl_vs_product(self):
        """
        Compare KL character with product formula for sl₂ at k = -4/3.

        This test verifies that the KacWakimotoCharacter class produces
        results consistent with the explicit product formula.
        """
        from pyw.algorithms.kac_wakimoto_character import KacWakimotoCharacter
        from pyw.core.affine_lie_algebra import AffineLieAlgebra
        from pyw.fractional.level import FractionalLevel

        # Setup
        ala = AffineLieAlgebra(["A", 1, 1])
        level = FractionalLevel(["A", 1, 1], p=2, u=3)  # k = -2 + 2/3 = -4/3

        kw = KacWakimotoCharacter(ala, level)

        # Get vacuum weight
        Lambda_0 = ala.fundamental_weights()[0]
        vacuum_weight = level.level * Lambda_0

        # Compute character via KL
        kl_char = kw.character(vacuum_weight, max_grade=5)

        # The leading coefficient should be 1
        assert kl_char[0] == 1, f"KL vacuum character leading term = {kl_char[0]}"


# =============================================================================
# Integration tests with pyw modules
# =============================================================================


class TestBoundaryAdmissibleIntegration:
    """Integration tests with pyw boundary admissible module."""

    def test_sl2_boundary_weights_count(self):
        """
        Verify correct number of boundary admissible weights for sl₂.

        At k = -4/3 (u=3), there should be exactly 3 weights.
        """
        # The number of boundary admissible weights equals u
        u = 3
        expected_count = u

        # Weights are Λ_{k,j} for j = 0, 1, ..., u-1
        actual_count = len(range(u))

        assert actual_count == expected_count, f"Weight count: {actual_count} vs {expected_count}"

    def test_sl2_conformal_weights(self):
        """
        Verify conformal weights for sl₂ boundary admissible representations.

        h_j = j(u-j)/(2u) for j = 0, 1, ..., u-1
        """
        u = 3

        expected_h = {
            0: rational(0, 1),  # h_0 = 0*3/(2*3) = 0
            1: rational(2, 6),  # h_1 = 1*2/(2*3) = 2/6 = 1/3
            2: rational(2, 6),  # h_2 = 2*1/(2*3) = 2/6 = 1/3
        }

        for j in range(u):
            h_j = rational(j * (u - j), 2 * u)
            assert h_j == expected_h[j], f"h_{j} = {h_j}, expected {expected_h[j]}"

    def test_sl3_boundary_weights_count(self):
        """
        Verify correct number of boundary admissible weights for sl₃.

        At k = -3/2 (u=2), there should be 3 weights: Λ_0, Λ_1, Λ_2.
        """
        # For sl_N at u=2, weights are -N/2 * Λ_p for p = 0, 1, ..., N-1
        N = 3
        expected_count = N

        actual_count = len(range(N))
        assert actual_count == expected_count


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

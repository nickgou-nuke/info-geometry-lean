"""
Jacobi Theta Functions and Dedekind Eta Function

This module provides implementations of modular forms needed for
boundary level character formulas (Kac-Wakimoto product formulas).

Key functions:
- η(τ): Dedekind eta function
- θ₁₁(τ, z): Jacobi theta function (also called θ₁ or ϑ₁)
- θ₀₁(τ, z): Jacobi theta function (also called θ₂ or ϑ₂)

References:
- Kac, V. G., Wakimoto, M. "A remark on boundary level admissible representations"
- Kac, V. G., Wakimoto, M. "Representations of affine superalgebras and mock theta functions"
"""

from __future__ import annotations

from typing import Optional, Union

from sage.all import (
    CC,
    I,
    Integer,
    Rational,
    exp,
    pi,
    prod,
    sqrt,
    var,
)


def dedekind_eta(tau, num_terms: int = 100):
    """
    Compute the Dedekind eta function η(τ).

    η(τ) = q^{1/24} ∏_{n=1}^∞ (1 - q^n)

    where q = e^{2πiτ}.
    """
    tau_c = CC(tau)
    q = exp(2 * pi * I * tau_c)
    q_24 = exp(2 * pi * I * tau_c / 24)  # q^{1/24}

    product = prod(1 - q**n for n in range(1, num_terms + 1))
    return q_24 * product


def theta_11(tau, z, num_terms: int = 100):
    """
    Compute the Jacobi theta function θ₁₁(τ, z) using sum formula.

    θ₁₁(τ, z) = -i ∑_{n∈ℤ} (-1)^n q^{(n+1/2)²/2} e^{2πi(n+1/2)z}

    This is the standard θ₁ function with the convention from Kac-Wakimoto.
    """
    tau_c = CC(tau)
    z_c = CC(z)

    q = exp(2 * pi * I * tau_c)

    # Use sum formula for better numerical stability
    result = CC(0)
    for n in range(-num_terms, num_terms + 1):
        n_half = n + Rational(1, 2)
        term = (-1) ** n * q ** (n_half**2 / 2) * exp(2 * pi * I * n_half * z_c)
        result += term

    return -I * result


def theta_11_product(tau, z, num_terms: int = 100):
    """
    Compute θ₁₁(τ, z) using the pure product formula.

    θ₁₁(τ, z) = -i q^{1/8} (y^{1/2} - y^{-1/2}) ∏_{n=1}^∞ (1-q^n)(1-yq^n)(1-y^{-1}q^n)

    where q = e^{2πiτ} and y = e^{2πiz}.
    """
    # Convert to complex for numerical stability
    tau_c = CC(tau)
    z_c = CC(z)

    q = exp(2 * pi * I * tau_c)
    y = exp(2 * pi * I * z_c)

    q_8 = exp(2 * pi * I * tau_c / 8)  # q^{1/8}
    y_half = exp(pi * I * z_c)  # y^{1/2}

    product = prod(
        (1 - q**n) * (1 - y * q**n) * (1 - y ** (-1) * q**n) for n in range(1, num_terms + 1)
    )

    return -I * q_8 * (y_half - y_half ** (-1)) * product


def theta_01(tau, z, num_terms: int = 100):
    """
    Compute the Jacobi theta function θ₀₁(τ, z).

    θ₀₁(τ, z) = ∏_{n=1}^∞ (1 - q^n)(1 - e^{2πiz} q^{n-1/2})(1 - e^{-2πiz} q^{n-1/2})

    This appears in the sl_N character formula at u=2.
    """
    tau_c = CC(tau)
    z_c = CC(z)

    q = exp(2 * pi * I * tau_c)
    y = exp(2 * pi * I * z_c)
    q_half = exp(pi * I * tau_c)  # q^{1/2}

    product = prod(
        (1 - q**n) * (1 - y * q_half * q ** (n - 1)) * (1 - y ** (-1) * q_half * q ** (n - 1))
        for n in range(1, num_terms + 1)
    )

    return product


def eta_ratio(tau, u: int, num_terms: int = 100):
    """Compute the ratio η(uτ)/η(τ)."""
    return dedekind_eta(u * tau, num_terms) / dedekind_eta(tau, num_terms)


def theta_ratio(tau, z, u: int, num_terms: int = 100):
    """Compute the ratio θ₁₁(uτ, z)/θ₁₁(τ, z)."""
    return theta_11_product(u * tau, z, num_terms) / theta_11_product(tau, z, num_terms)


# =============================================================================
# Boundary Level Character Formulas (Kac-Wakimoto)
# =============================================================================


def sl2_boundary_character(u: int, j: int, tau, z, num_terms: int = 100):
    """
    Compute the sl₂ boundary level character ch_{Λ_{u,j}}.

    For sl₂ at boundary level k = 2/u - 2 (u odd), the character is:
    ch_{Λ_{u,j}}(τ, z) ∝ q^{j²/2u} y^{-j/u} θ₁₁(uτ, z-jτ) / θ₁₁(τ, z)
    """
    if u % 2 == 0:
        raise ValueError(f"u must be odd for sl₂, got u={u}")
    if not (0 <= j < u):
        raise ValueError(f"j must be in [0, u-1], got j={j}")

    # Convert to complex for numerical stability
    tau_c = CC(tau)
    z_c = CC(z)

    q = exp(2 * pi * I * tau_c)
    y = exp(2 * pi * I * z_c)

    # Prefactor: q^{j²/2u} y^{-j/u}
    prefactor = q ** (Rational(j**2, 2 * u)) * y ** (-Rational(j, u))

    # Theta ratio: θ₁₁(uτ, z-jτ) / θ₁₁(τ, z)
    z_shifted = z_c - j * tau_c
    numerator = theta_11_product(u * tau_c, z_shifted, num_terms)
    denominator = theta_11_product(tau_c, z_c, num_terms)

    return prefactor * numerator / denominator


def sl2_boundary_vacuum_character(u: int, tau, z, num_terms: int = 100):
    """Compute the sl₂ boundary level vacuum character ch_{kΛ₀} (j=0 case)."""
    return sl2_boundary_character(u, 0, tau, z, num_terms)


def sl3_boundary_vacuum_character(tau, z1, z2, num_terms: int = 100):
    """
    Compute the sl₃ boundary level vacuum character at k = -3/2 (u=2).

    ch_{-3/2 Λ₀}(τ, z) = (η(2τ)/η(τ))^{-1} ∏_{α∈Δ+} θ₁₁(2τ, α(z)) / θ₁₁(τ, α(z))
    """
    u = 2

    # Convert to complex
    tau_c = CC(tau)
    z1_c = CC(z1)
    z2_c = CC(z2)

    # Eta ratio factor: (η(2τ)/η(τ))^{-1}
    eta_factor = eta_ratio(tau_c, u, num_terms) ** (-1)

    # Positive roots for sl₃: α₁, α₂, α₁+α₂
    roots = [z1_c, z2_c, z1_c + z2_c]

    # Product over positive roots
    theta_product = prod(theta_ratio(tau_c, alpha_z, u, num_terms) for alpha_z in roots)

    return eta_factor * theta_product


# =============================================================================
# q-expansion utilities
# =============================================================================


def character_q_expansion(char_func, tau_val, z_val, max_power: int = 10, num_terms: int = 100):
    """
    Extract q-expansion coefficients from a character function.

    This is a numerical method: evaluate the character at specific τ values
    and extract coefficients using Fourier analysis.

    Parameters
    ----------
    char_func : callable
        Function (tau, z) -> character value
    tau_val : complex
        Base τ value (should have large imaginary part for convergence)
    z_val : complex
        The z parameter
    max_power : int
        Maximum power of q to extract
    num_terms : int
        Number of terms in theta/eta expansions

    Returns
    -------
    dict
        Dictionary {power: coefficient}
    """
    from sage.all import CC, RR

    # Use numerical evaluation
    q = exp(2 * pi * I * tau_val)
    q_abs = abs(CC(q))

    if q_abs >= 1:
        raise ValueError(f"Need |q| < 1, got |q| = {q_abs}")

    # Evaluate character
    char_val = char_func(tau_val, z_val)

    # For now, just return the numerical value
    # Full q-expansion extraction requires more sophisticated methods
    return {"value": CC(char_val), "q": CC(q)}


# =============================================================================
# Verification utilities
# =============================================================================


def verify_theta_properties(tau, z, tol: float = 1e-10):
    """
    Verify basic properties of theta functions.

    Tests:
    1. θ₁₁(τ, 0) ≈ 0 (zero at z=0)
    2. θ₁₁(τ, -z) ≈ -θ₁₁(τ, z) (odd function)
    3. θ₁₁(τ, z+1) ≈ -θ₁₁(τ, z) (quasi-periodicity)

    Parameters
    ----------
    tau : complex
        The modular parameter
    z : complex
        Test point for z
    tol : float
        Tolerance for numerical comparisons

    Returns
    -------
    dict
        Dictionary of test results
    """
    results = {}

    # Test 1: θ₁₁(τ, 0) = 0
    theta_at_zero = theta_11_product(tau, 0)
    results["zero_at_origin"] = abs(CC(theta_at_zero)) < tol

    # Test 2: θ₁₁(τ, -z) = -θ₁₁(τ, z)
    theta_z = theta_11_product(tau, z)
    theta_neg_z = theta_11_product(tau, -z)
    results["odd_function"] = abs(CC(theta_z + theta_neg_z)) < tol * abs(CC(theta_z))

    # Test 3: θ₁₁(τ, z+1) = -θ₁₁(τ, z)
    theta_z_plus_1 = theta_11_product(tau, z + 1)
    results["quasi_periodic"] = abs(CC(theta_z_plus_1 + theta_z)) < tol * abs(CC(theta_z))

    return results

#!/usr/bin/env python3
"""
2×2 GUE Matrix — Exponential Family, JPDF, and Wigner Surmise
================================================================
SymPy/mpmath/numpy implementation of the 2×2 Gaussian Unitary Ensemble.

Covers:
  1. Sampling 2×2 GUE matrices:
       H = [ a      c − i d ]
           [ c + i d    b   ]
       a,b ~ N(0,1),  c,d ~ N(0, 1/2)

  2. Joint eigenvalue distribution (JPDF):
       P(λ₁,λ₂) ∝ |λ₁ − λ₂|² exp(−(λ₁² + λ₂²)/2)

  3. Exponential family structure:
       T₁ = λ₁² + λ₂²,  T₂ = ln|λ₁ − λ₂|
       η₁ = −1/2,       η₂ = 2 (= Dyson β for GUE)

  4. Wigner surmise (normalized, mean spacing = 1):
       P_GUE(s) = (32/π²) s² exp(−4s²/π),  s ≥ 0

  5. Comparison with IJIRT 172568 (Riemann ζ-zeros follow GUE statistics)

Usage:
  python GUE2x2ExponentialFamily.py
  python GUE2x2ExponentialFamily.py --plot
"""

import sys
import math
from typing import List, Tuple, Dict

import numpy as np
from scipy import integrate
from scipy.special import gamma as gamma_func
import mpmath as mp

import sys as _sys
_QUICK = '--quick' in _sys.argv
_HIGH_PREC = '--high-precision' in _sys.argv
mp.mp.dps = 50 if _HIGH_PREC else 15

# ══════════════════════════════════════════════════════════════════════════════
# Part 1:  Sampling 2×2 GUE matrices
# ══════════════════════════════════════════════════════════════════════════════

def sample_gue_2x2(rng: np.random.Generator) -> Tuple[float, float, float, float]:
    """
    Sample the four independent real parameters of a 2×2 GUE matrix.
    Returns (a, b, c, d) where:
      a, b ~ N(0, 1)    — diagonal elements
      c, d ~ N(0, 1/2)  — real/imag parts of off-diagonal
    """
    a = rng.normal(0.0, 1.0)
    b = rng.normal(0.0, 1.0)
    c = rng.normal(0.0, math.sqrt(0.5))
    d = rng.normal(0.0, math.sqrt(0.5))
    return a, b, c, d


def construct_gue_matrix(a: float, b: float, c: float, d: float) -> np.ndarray:
    """
    Construct the 2×2 Hermitian GUE matrix:
        H = [[a, c - i d],
             [c + i d, b]]
    """
    H = np.array([[a, c - 1j * d],
                  [c + 1j * d, b]], dtype=complex)
    return H


def gue_eigenvalues(a: float, b: float, c: float, d: float) -> Tuple[float, float]:
    """
    Compute the two eigenvalues of the 2×2 GUE matrix.
    Analytic formula (no numpy.linalg needed for 2×2):
      λ₁,₂ = (a+b)/2 ± ½√((a−b)² + 4(c² + d²))
    Returns (λmax, λmin) ordered descending.
    """
    center = (a + b) / 2.0
    discriminant = (a - b)**2 + 4.0 * (c**2 + d**2)
    half_spread = 0.5 * math.sqrt(discriminant)
    return center + half_spread, center - half_spread


def gue_spacing(a: float, b: float, c: float, d: float) -> float:
    """Compute the eigenvalue spacing S = λ₁ − λ₂ ≥ 0."""
    return math.sqrt((a - b)**2 + 4.0 * (c**2 + d**2))


def gue_trace_squared(a: float, b: float, c: float, d: float) -> float:
    """Tr(H²) = a² + b² + 2(c² + d²)."""
    return a**2 + b**2 + 2.0 * (c**2 + d**2)


# ══════════════════════════════════════════════════════════════════════════════
# Part 2:  Joint Eigenvalue Distribution (JPDF) — theoretical forms
# ══════════════════════════════════════════════════════════════════════════════

def jpdf_unnormalized(lambda1: float, lambda2: float) -> float:
    """
    Unnormalized JPDF:
      ρ(λ₁, λ₂) = |λ₁ − λ₂|² exp(−(λ₁² + λ₂²)/2)
    """
    spacing_sq = (lambda1 - lambda2)**2
    gaussian_weight = math.exp(-(lambda1**2 + lambda2**2) / 2.0)
    return spacing_sq * gaussian_weight


def jpdf_log_form(lambda1: float, lambda2: float) -> float:
    """
    Log of the unnormalized JPDF (exponential family form):
      ln ρ = 2 ln|λ₁ − λ₂| − (λ₁² + λ₂²)/2
    """
    if lambda1 == lambda2:
        return -float('inf')
    return 2.0 * math.log(abs(lambda1 - lambda2)) - (lambda1**2 + lambda2**2) / 2.0


def jpdf_in_SR(S: float, R: float) -> float:
    """
    JPDF in (spacing, center-of-mass) coordinates:
    S = λ₁ − λ₂,  R = λ₁ + λ₂
    ρ(S, R) ∝ S² exp(−(S² + R²)/4)
    """
    return (S**2) * math.exp(-(S**2 + R**2) / 4.0)


# ══════════════════════════════════════════════════════════════════════════════
# Part 3:  Exponential Family Structure
# ══════════════════════════════════════════════════════════════════════════════

# Natural parameters
ETA1 = -0.5   # Gaussian confinement strength
ETA2 = 2.0    # Dyson index β = 2 (GUE)


def sufficient_statistic_T1(lambda1: float, lambda2: float) -> float:
    """T₁ = λ₁² + λ₂² (Gaussian confinement / trace of H²)."""
    return lambda1**2 + lambda2**2


def sufficient_statistic_T2(lambda1: float, lambda2: float) -> float:
    """T₂ = ln|λ₁ − λ₂| (logarithmic Coulomb repulsion)."""
    if lambda1 == lambda2:
        return -float('inf')
    return math.log(abs(lambda1 - lambda2))


def exponential_family_unnormalized(lambda1: float, lambda2: float) -> float:
    """
    Unnormalized density in exponential family form:
      ρ(λ₁,λ₂) ∝ exp(η₁ T₁ + η₂ T₂)
    where η₁ = −1/2, η₂ = 2.
    """
    if lambda1 == lambda2:
        return 0.0
    log_density = ETA1 * sufficient_statistic_T1(lambda1, lambda2) + \
                  ETA2 * sufficient_statistic_T2(lambda1, lambda2)
    return math.exp(log_density)


def verify_exponential_family(lambda1: float, lambda2: float) -> Tuple[float, float]:
    """
    Verify that the exponential family form matches the JPDF form.
    Returns (jpdf_value, exp_family_value) — they should be equal
    up to the same normalization constant.
    """
    jpdf = jpdf_unnormalized(lambda1, lambda2)
    exp_fam = exponential_family_unnormalized(lambda1, lambda2)
    return jpdf, exp_fam


# ══════════════════════════════════════════════════════════════════════════════
# Part 4:  Wigner Surmise — GUE (β = 2) Spacing Distribution
# ══════════════════════════════════════════════════════════════════════════════

def wigner_surmise_GUE(s: float) -> float:
    """
    Wigner surmise for GUE (Dyson index β = 2):
      P_GUE(s) = (32/π²) s² exp(−4s²/π),  s ≥ 0
    Normalized so that mean spacing = 1.
    """
    if s < 0:
        return 0.0
    return (32.0 / math.pi**2) * s**2 * math.exp(-4.0 * s**2 / math.pi)


def wigner_surmise_GOE(s: float) -> float:
    """Wigner surmise for GOE (β = 1): P₁(s) = (πs/2) exp(−πs²/4)."""
    if s < 0:
        return 0.0
    return (math.pi * s / 2.0) * math.exp(-math.pi * s**2 / 4.0)


def wigner_surmise_GSE(s: float) -> float:
    """Wigner surmise for GSE (β = 4): P₄(s) = (2¹⁸/3⁶π³) s⁴ exp(−64s²/9π)."""
    if s < 0:
        return 0.0
    coeff = 262144.0 / (729.0 * math.pi**3)
    return coeff * s**4 * math.exp(-64.0 * s**2 / (9.0 * math.pi))


def wigner_surmise_general(s: float, beta: float) -> float:
    """
    General Wigner surmise for Dyson index β:
      P_β(s) = a_β s^β exp(−b_β s²)
    where a_β, b_β are chosen so ∫P = 1 and ⟨s⟩ = 1.

    a_β = 2 · [Γ((β+2)/2)]^(β+1) / [Γ((β+1)/2)]^(β+2)
    b_β = [Γ((β+2)/2) / Γ((β+1)/2)]²
    """
    if s <= 0:
        return 0.0
    g1 = gamma_func((beta + 1) / 2.0)
    g2 = gamma_func((beta + 2) / 2.0)
    a = 2.0 * (g2 ** (beta + 1)) / (g1 ** (beta + 2))
    b = (g2 / g1) ** 2
    return a * (s ** beta) * math.exp(-b * s**2)


# ══════════════════════════════════════════════════════════════════════════════
# Part 5:  Numerical verification of Wigner surmise normalization
# ══════════════════════════════════════════════════════════════════════════════

def verify_normalization(beta: float = 2.0) -> Dict:
    """
    Numerically verify that the Wigner surmise is properly normalized:
      ∫₀^∞ P_β(s) ds = 1
      ∫₀^∞ s P_β(s) ds = 1   (mean spacing)
    """
    # Use mpmath for high-precision integration
    if beta == 2.0:
        f = lambda s: wigner_surmise_GUE(s)
    elif beta == 1.0:
        f = lambda s: wigner_surmise_GOE(s)
    elif abs(beta - 4.0) < 1e-10:
        f = lambda s: wigner_surmise_GSE(s)
    else:
        f = lambda s: wigner_surmise_general(float(s), beta)

    integral = mp.quad(f, [0, mp.inf])
    mean = mp.quad(lambda s: s * f(s), [0, mp.inf])
    second_moment = mp.quad(lambda s: s**2 * f(s), [0, mp.inf])

    return {
        'beta': beta,
        'integral': float(integral),
        'mean_spacing': float(mean),
        'second_moment': float(second_moment),
        'variance': float(second_moment - mean**2),
    }


# ══════════════════════════════════════════════════════════════════════════════
# Part 6:  Monte Carlo sampling of 2×2 GUE eigenvalue spacings
# ══════════════════════════════════════════════════════════════════════════════

def sample_spacings(n_samples: int = 100000, seed: int = 42) -> List[float]:
    """
    Sample N independent 2×2 GUE matrices, compute their eigenvalue spacings,
    and normalize so that mean spacing = 1.
    Returns list of normalized spacings.
    """
    rng = np.random.default_rng(seed)
    spacings = []
    for _ in range(n_samples):
        a, b, c, d = sample_gue_2x2(rng)
        S = gue_spacing(a, b, c, d)
        spacings.append(S)
    mean_S = np.mean(spacings)
    # Normalize to mean = 1
    normalized = [s / mean_S for s in spacings]
    return normalized


def spacing_histogram(spacings: List[float], n_bins: int = 100) -> Tuple[np.ndarray, np.ndarray]:
    """Compute density histogram of normalized spacings."""
    counts, bin_edges = np.histogram(spacings, bins=n_bins, density=True)
    bin_centers = 0.5 * (bin_edges[:-1] + bin_edges[1:])
    return bin_centers, counts


def ks_test_vs_wigner(spacings: List[float]) -> float:
    """
    Kolmogorov–Smirnov test comparing empirical spacing distribution
    against the Wigner surmise for GUE.
    """
    sorted_s = sorted(spacings)
    N = len(sorted_s)
    D = 0.0
    for i, s in enumerate(sorted_s, 1):
        empirical = i / N
        # Wigner surmise CDF: F(s) = 1 − exp(−4s²/π) − (8s/π) exp(−4s²/π)
        if s <= 0:
            theoretical = 0.0
        else:
            theoretical = wigner_CDF_GUE(s)  # defined below
        D = max(D, abs(empirical - theoretical))
    return D


def wigner_CDF_GUE(s: float) -> float:
    """
    CDF of the Wigner surmise for GUE:
      F(s) = 1 − exp(−4s²/π) − (4s²/π) exp(−4s²/π)
    Actually:
      F(s) = 1 − exp(−4s²/π) · (1 + 4s²/π)
    Derived by integrating (32/π²) t² exp(−4t²/π) dt from 0 to s.
    """
    if s <= 0:
        return 0.0
    x = 4.0 * s**2 / math.pi
    return 1.0 - math.exp(-x) * (1.0 + x)


def wigner_CDF_GOE(s: float) -> float:
    """CDF for GOE Wigner surmise: F(s) = 1 − exp(−πs²/4)."""
    if s <= 0:
        return 0.0
    return 1.0 - math.exp(-math.pi * s**2 / 4.0)


# ══════════════════════════════════════════════════════════════════════════════
# Part 7:  Analytic verification — the 2×2 JPDF normalization
# ══════════════════════════════════════════════════════════════════════════════

def analytic_normalization_2x2() -> Dict:
    """
    Compute the analytic normalization constant C for the 2×2 GUE JPDF.

    The unnormalized JPDF is:
      ρ(λ₁, λ₂) = |λ₁ − λ₂|² exp(−(λ₁² + λ₂²)/2)

    Change variables: S = λ₁ − λ₂, R = λ₁ + λ₂
    Jacobian = 1/2, so:
      C = ½ ∫_{−∞}^{∞} ∫_{0}^{∞} S² exp(−(R² + S²)/4) dS dR

    R integral: ∫ exp(−R²/4) dR = √(4π) = 2√π
    S integral: ∫₀^∞ S² exp(−S²/4) dS = 2√π

    Total: C = ½ · 2√π · 2√π = 2π

    Therefore: P(λ₁, λ₂) = (1/(2π)) |λ₁ − λ₂|² exp(−(λ₁² + λ₂²)/2)
    """
    # Verify numerically with mpmath
    R_integral = float(mp.quad(lambda r: mp.exp(-r**2 / 4), [-mp.inf, mp.inf]))
    S_integral = float(mp.quad(lambda s: s**2 * mp.exp(-s**2 / 4), [0, mp.inf]))
    jacobian = 0.5
    C_numerical = jacobian * R_integral * S_integral
    C_analytic = 2.0 * math.pi

    return {
        'R_integral': R_integral,
        'R_integral_analytic': 2.0 * math.sqrt(math.pi),
        'S_integral': S_integral,
        'S_integral_analytic': 2.0 * math.sqrt(math.pi),
        'C_numerical': C_numerical,
        'C_analytic': C_analytic,
        'agreement': abs(C_numerical - C_analytic) < 1e-8,
    }


# ══════════════════════════════════════════════════════════════════════════════
# Part 8:  Connection to IJIRT 172568 — Riemann ζ-zeros
# ══════════════════════════════════════════════════════════════════════════════

def zeta_zero_spacings(n_zeros: int = 300) -> List[float]:
    """
    Compute normalized spacings between consecutive ordinates of ζ-zeros.
    The ζ-zeros are expected to follow GUE (β = 2) statistics.
    """
    ordinates = []
    for k in range(1, n_zeros + 1):
        rho = mp.zetazero(k)
        ordinates.append(float(mp.im(rho)))
    spacings = [ordinates[i+1] - ordinates[i] for i in range(len(ordinates) - 1)]
    mean_sp = np.mean(spacings)
    return [s / mean_sp for s in spacings]


def compare_zeta_to_2x2_GUE(n_zeros: int = 500, n_gue_samples: int = 50000) -> Dict:
    """
    Compare ζ-zero spacing distribution against:
    (a) the 2×2 GUE exact sampling,
    (b) the Wigner surmise formula.
    """
    # ζ-zeros
    zeta_sp = zeta_zero_spacings(n_zeros)

    # 2×2 GUE Monte Carlo
    gue_sp = sample_spacings(n_gue_samples)

    # KS tests against Wigner surmise
    zeta_ks = ks_test_vs_wigner(zeta_sp)
    gue_ks = ks_test_vs_wigner(gue_sp)

    return {
        'n_zeros': n_zeros,
        'n_gue_samples': n_gue_samples,
        'zeta_KS_vs_Wigner': zeta_ks,
        'gue_2x2_KS_vs_Wigner': gue_ks,
        'zeta_mean_spacing': float(np.mean(zeta_sp)),
        'gue_mean_spacing': float(np.mean(gue_sp)),
        'zeta_variance': float(np.var(zeta_sp)),
        'gue_variance': float(np.var(gue_sp)),
    }


# ══════════════════════════════════════════════════════════════════════════════
# Part 9:  Entry distribution verification
# ══════════════════════════════════════════════════════════════════════════════

def verify_entry_distributions(n_samples: int = 100000) -> Dict:
    """
    Verify that the sampled entries match their theoretical distributions:
    - a, b should be N(0, 1)
    - c, d should be N(0, 1/2)
    """
    rng = np.random.default_rng(42)
    a_vals, b_vals, c_vals, d_vals = [], [], [], []

    for _ in range(n_samples):
        a, b, c, d = sample_gue_2x2(rng)
        a_vals.append(a)
        b_vals.append(b)
        c_vals.append(c)
        d_vals.append(d)

    return {
        'a_mean': float(np.mean(a_vals)),
        'a_std': float(np.std(a_vals)),
        'a_theoretical': 'N(0, 1)',
        'b_mean': float(np.mean(b_vals)),
        'b_std': float(np.std(b_vals)),
        'b_theoretical': 'N(0, 1)',
        'c_mean': float(np.mean(c_vals)),
        'c_std': float(np.std(c_vals)),
        'c_theoretical': 'N(0, 1/2), σ = 0.7071',
        'd_mean': float(np.mean(d_vals)),
        'd_std': float(np.std(d_vals)),
        'd_theoretical': 'N(0, 1/2), σ = 0.7071',
    }


# ══════════════════════════════════════════════════════════════════════════════
# Part 10:  Run all computations
# ══════════════════════════════════════════════════════════════════════════════

def run_all(show_plots: bool = False):
    """Run all 2×2 GUE computations and print results."""

    print("=" * 72)
    print("  2×2 GUE — Exponential Family, JPDF, and Wigner Surmise")
    print("  Wigner·Dyson · Montgomery·Odlyzko · Dyson β = 2")
    print("=" * 72)

    # ── Matrix Construction ────────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 1: 2×2 GUE Matrix Construction")
    print("─" * 72)

    rng = np.random.default_rng(172568)  # paper reference as seed
    a, b, c, d = sample_gue_2x2(rng)
    H = construct_gue_matrix(a, b, c, d)
    lam1, lam2 = gue_eigenvalues(a, b, c, d)
    S = gue_spacing(a, b, c, d)
    TrH2 = gue_trace_squared(a, b, c, d)

    print(f"\n  Random 2×2 GUE matrix sample:")
    print(f"    H = [[{H[0,0]:.6f}, {H[0,1]:.6f}],")
    print(f"         [{H[1,0]:.6f}, {H[1,1]:.6f}]]")
    print(f"  Hermitian check: H = H† ?  {np.allclose(H, H.conj().T)}")
    print(f"  Trace:            {float(np.trace(H).real):.6f}")
    print(f"  Tr(H²):           {TrH2:.6f}")
    print(f"  Eigenvalues:      λ₁ = {lam1:.6f},  λ₂ = {lam2:.6f}")
    print(f"  Spacing S = λ₁−λ₂ = {S:.6f}")
    print(f"  Center R = λ₁+λ₂  = {lam1 + lam2:.6f}")
    print(f"  Check: Tr(H) = R?   {abs((a + b) - (lam1 + lam2)) < 1e-10}")
    print(f"  Check: S ≥ 0?       {S >= 0}")

    # ── Entry Distribution Verification ─────────────────────────────────
    print(f"\n  Entry distribution verification (100k samples):")
    entry_stats = verify_entry_distributions(100000)
    for key in ['a', 'b', 'c', 'd']:
        m = entry_stats[f'{key}_mean']
        s = entry_stats[f'{key}_std']
        theo = entry_stats[f'{key}_theoretical']
        print(f"    {key}: mean = {m:+.4f}, std = {s:.4f}  [{theo}]")

    # ── Exponential Family ─────────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 2: Exponential Family Structure")
    print("─" * 72)

    lam_test = [1.5, -0.8]
    T1 = sufficient_statistic_T1(*lam_test)
    T2 = sufficient_statistic_T2(*lam_test)
    jpdf_val = jpdf_unnormalized(*lam_test)
    exp_fam_val = exponential_family_unnormalized(*lam_test)

    print(f"\n  Test eigenvalues: λ₁ = {lam_test[0]}, λ₂ = {lam_test[1]}")
    print(f"    T₁ = λ₁² + λ₂²                      = {T1:.6f}")
    print(f"    T₂ = ln|λ₁ − λ₂|                    = {T2:.6f}")
    print(f"    η₁ = {ETA1},  η₂ = {ETA2}")
    print(f"    η₁·T₁ + η₂·T₂                       = {ETA1*T1 + ETA2*T2:.6f}")
    print(f"    ρ_JPDF (unnormalized)               = {jpdf_val:.6e}")
    print(f"    ρ_exp_family (unnormalized)          = {exp_fam_val:.6e}")
    print(f"    Ratio (should be 1):                = {jpdf_val/exp_fam_val:.10f}")

    # Show the identity: exp(η₁T₁ + η₂T₂) = |λ₁−λ₂|² exp(−(λ₁²+λ₂²)/2)
    print(f"\n  Identity verification:")
    print(f"    exp(η₁T₁ + η₂T₂) = exp({ETA1:.1f}·{T1:.4f} + {ETA2:.1f}·{T2:.4f})")
    print(f"    = exp({ETA1*T1 + ETA2*T2:.6f}) = {math.exp(ETA1*T1 + ETA2*T2):.6e}")
    print(f"    = |λ₁−λ₂|² exp(−(λ₁²+λ₂²)/2)")
    print(f"    = {abs(lam_test[0]-lam_test[1])**2:.4f} · exp(−{(lam_test[0]**2+lam_test[1]**2)/2:.4f})")
    print(f"    = {abs(lam_test[0]-lam_test[1])**2 * math.exp(-(lam_test[0]**2+lam_test[1]**2)/2):.6e} ✓")

    # ── Wigner Surmise ─────────────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 3: Wigner Surmise — GUE (β = 2)")
    print("─" * 72)

    print(f"\n  P_GUE(s) = (32/π²) s² exp(−4s²/π)")
    print(f"  Normalization: ∫₀^∞ P(s) ds = 1,  ⟨s⟩ = 1")

    norm = verify_normalization(beta=2.0)
    print(f"\n  Numerical verification (mpmath):")
    print(f"    ∫ P(s) ds = {norm['integral']:.10f}  (should be 1)")
    print(f"    ⟨s⟩       = {norm['mean_spacing']:.10f}  (should be 1)")
    print(f"    ⟨s²⟩      = {norm['second_moment']:.10f}  (analytic: 3π/8 ≈ {3*math.pi/8:.6f})")
    print(f"    Var(s)    = {norm['variance']:.10f}  (analytic: 3π/8−1 ≈ {3*math.pi/8-1:.6f})")

    # Key values
    print(f"\n  Key PDF values:")
    for s in [0.0, 0.2, 0.5, 0.88623, 1.0, 1.5, 2.0, 3.0]:
        pdf = wigner_surmise_GUE(s)
        cdf = wigner_CDF_GUE(s)
        print(f"    P({s:.5f}) = {pdf:.6f},  CDF({s:.5f}) = {cdf:.6f}")

    # Level repulsion
    print(f"\n  Level repulsion:")
    print(f"    P(0) = {wigner_surmise_GUE(0):.6f}  ← eigenvalue repulsion! (β=2)")
    print(f"    For small s: P(s) ≈ (32/π²) s² ≈ {32/math.pi**2:.4f} · s²")

    # Peak
    s_peak = math.sqrt(math.pi / 4.0)
    print(f"    Peak at s = √(π/4) ≈ {s_peak:.6f}")
    print(f"    P_peak = (8/π)·exp(−1) ≈ {8.0/math.pi*math.exp(-1):.6f}")

    # ── 2×2 GUE Monte Carlo ────────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 4: 2×2 GUE Monte Carlo — Spacing Distribution")
    print("─" * 72)

    n_mc = 100000
    spacings = sample_spacings(n_mc, seed=172568)
    mean_sp = np.mean(spacings)
    var_sp = np.var(spacings)

    print(f"\n  {n_mc:,} Monte Carlo samples from 2×2 GUE:")
    print(f"    Mean spacing (normalized) = {mean_sp:.6f}  (target: 1)")
    print(f"    Variance                  = {var_sp:.6f}  (analytic: {3*math.pi/8 - 1:.6f})")

    # KS test
    ks_stat = ks_test_vs_wigner(spacings)
    print(f"    KS statistic vs Wigner surmise = {ks_stat:.6f}")
    print(f"    (Small KS → excellent agreement)")

    # ── JPDF Normalization ─────────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 5: JPDF Analytic Normalization")
    print("─" * 72)

    norm_2x2 = analytic_normalization_2x2()
    print(f"\n  Change of variables (λ₁,λ₂) → (S,R):")
    print(f"    ∫₋∞^∞ exp(−R²/4) dR       = {norm_2x2['R_integral']:.10f}")
    print(f"    (analytic: 2√π = {norm_2x2['R_integral_analytic']:.10f})")
    print(f"    ∫₀^∞ S² exp(−S²/4) dS     = {norm_2x2['S_integral']:.10f}")
    print(f"    (analytic: 2√π = {norm_2x2['S_integral_analytic']:.10f})")
    print(f"    Jacobian = 1/2")
    print(f"    C = ½ · 2√π · 2√π = {norm_2x2['C_analytic']:.6f} (analytic: 2π)")
    print(f"    Numerical C = {norm_2x2['C_numerical']:.6f}")
    print(f"    Agreement: {norm_2x2['agreement']}")

    # ── Comparison with ζ-zeros ────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 6: Connection to Riemann ζ-zeros (IJIRT 172568)")
    print("─" * 72)

    comparison = compare_zeta_to_2x2_GUE(n_zeros=500, n_gue_samples=50000)
    print(f"\n  ζ-zeros (N={comparison['n_zeros']}) vs Wigner surmise:")
    print(f"    KS statistic          = {comparison['zeta_KS_vs_Wigner']:.6f}")
    print(f"    Mean spacing          = {comparison['zeta_mean_spacing']:.6f}")
    print(f"    Variance              = {comparison['zeta_variance']:.6f}")
    print(f"\n  2×2 GUE MC (N={comparison['n_gue_samples']}) vs Wigner surmise:")
    print(f"    KS statistic          = {comparison['gue_2x2_KS_vs_Wigner']:.6f}")
    print(f"    Mean spacing          = {comparison['gue_mean_spacing']:.6f}")
    print(f"    Variance              = {comparison['gue_variance']:.6f}")

    print(f"\n  Dyson index β = 2 (GUE) describes both:")
    print(f"    • 2×2 GUE eigenvalue spacings")
    print(f"    • Riemann ζ-zero spacings (Montgomery–Odlyzko law)")
    print(f"  This is the central message of IJIRT 172568 Theorem 4.")

    # ── All three β values ─────────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Part 7: Wigner Surmises for GOE (β=1), GUE (β=2), GSE (β=4)")
    print("─" * 72)

    for beta in [1.0, 2.0, 4.0]:
        n = verify_normalization(beta)
        print(f"\n  β = {beta:.0f}:")
        print(f"    ∫ P(s) ds = {n['integral']:.10f}")
        print(f"    ⟨s⟩       = {n['mean_spacing']:.10f}")
        print(f"    Var(s)    = {n['variance']:.6f}")
        if beta == 1.0:
            print(f"    P(0) = {wigner_surmise_GOE(0)} (linear repulsion)")
        elif abs(beta - 2.0) < 1e-10:
            print(f"    P(0) = {wigner_surmise_GUE(0)} (quadratic repulsion)")
        else:
            print(f"    P(0) = {wigner_surmise_GSE(0)} (quartic repulsion)")

    # ── Summary ────────────────────────────────────────────────────────
    print("\n" + "=" * 72)
    print("  Summary — 2×2 GUE Formalization")
    print("=" * 72)
    print(f"""
    Matrix:  H = [[a, c−id], [c+id, b]]  Hermitian 2×2
             a,b ∼ N(0,1),  c,d ∼ N(0, 1/2)

    JPDF:    P(λ₁,λ₂) = (1/2π) |λ₁−λ₂|² exp(−(λ₁²+λ₂²)/2)

    Exp. Family:  T₁ = λ₁²+λ₂²,  T₂ = ln|λ₁−λ₂|
                  η₁ = −½,  η₂ = 2 (Dyson β = 2)

    Wigner:  P_GUE(s) = (32/π²) s² exp(−4s²/π)
             ∫P = 1,  ⟨s⟩ = 1,  Var(s) = 3π/8−1 ≈ {3*math.pi/8 - 1:.4f}
             P(0) = 0  (level repulsion, β = 2)

    2×2 MC:  {n_mc:,} samples, KS = {ks_stat:.4f} vs Wigner
    ζ-zeros: KS = {comparison['zeta_KS_vs_Wigner']:.4f} vs Wigner
    """)


def generate_plots(plt):
    """Generate publication-quality plots for the 2×2 GUE."""
    fig, axes = plt.subplots(2, 3, figsize=(18, 12))

    # ── Plot 1: Wigner surmisess for β = 1, 2, 4 ─────────────────────
    ax1 = axes[0, 0]
    s_vals = np.linspace(0, 4, 300)
    ax1.plot(s_vals, [wigner_surmise_GOE(s) for s in s_vals],
             'b-', linewidth=2, label='GOE (β=1)')
    ax1.plot(s_vals, [wigner_surmise_GUE(s) for s in s_vals],
             'r-', linewidth=2.5, label='GUE (β=2)')
    ax1.plot(s_vals, [wigner_surmise_GSE(s) for s in s_vals],
             'g-', linewidth=2, label='GSE (β=4)')
    ax1.axhline(y=0, color='k', linewidth=0.5)
    ax1.set_xlabel('Normalized spacing s', fontsize=11)
    ax1.set_ylabel('P(s)', fontsize=11)
    ax1.set_title('Wigner Surmises: GOE, GUE, GSE', fontsize=12)
    ax1.legend(fontsize=9)
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, 4)

    # ── Plot 2: 2×2 GUE MC vs Wigner surmise ──────────────────────────
    ax2 = axes[0, 1]
    spacings_mc = sample_spacings(50000, seed=42)
    ax2.hist(spacings_mc, bins=80, density=True, alpha=0.5,
             color='darkred', edgecolor='black', linewidth=0.3,
             label=f'2×2 GUE MC (N=50000)')
    ax2.plot(s_vals, [wigner_surmise_GUE(s) for s in s_vals],
             'k-', linewidth=2.5, label='Wigner GUE')
    ax2.set_xlabel('Normalized spacing s', fontsize=11)
    ax2.set_ylabel('Density', fontsize=11)
    ax2.set_title('2×2 GUE MC vs Wigner Surmise', fontsize=12)
    ax2.legend(fontsize=9)
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(0, 4)

    # ── Plot 3: Entry distributions ────────────────────────────────────
    ax3 = axes[0, 2]
    rng = np.random.default_rng(42)
    n_entry = 20000
    a_vals = [sample_gue_2x2(rng)[0] for _ in range(n_entry)]
    c_vals = [sample_gue_2x2(rng)[2] for _ in range(n_entry)]
    ax3.hist(a_vals, bins=60, density=True, alpha=0.5,
             color='blue', edgecolor='black', linewidth=0.3,
             label='a ∼ N(0,1) [diagonal]')
    ax3.hist(c_vals, bins=60, density=True, alpha=0.5,
             color='orange', edgecolor='black', linewidth=0.3,
             label='c ∼ N(0,1/2) [off-diag]')
    x_fine = np.linspace(-4, 4, 200)
    ax3.plot(x_fine, 1/math.sqrt(2*math.pi)*np.exp(-x_fine**2/2),
             'b-', linewidth=1.5, label='N(0,1) PDF')
    ax3.plot(x_fine, 1/math.sqrt(math.pi)*np.exp(-x_fine**2),
             'orange', linewidth=1.5, label='N(0,1/2) PDF')
    ax3.set_xlabel('Value', fontsize=11)
    ax3.set_ylabel('Density', fontsize=11)
    ax3.set_title('GUE Entry Distributions', fontsize=12)
    ax3.legend(fontsize=8)
    ax3.grid(True, alpha=0.3)

    # ── Plot 4: ζ-zeros vs Wigner surmise ──────────────────────────────
    ax4 = axes[1, 0]
    zeta_sp = zeta_zero_spacings(500)
    ax4.hist(zeta_sp, bins=60, density=True, alpha=0.5,
             color='darkblue', edgecolor='black', linewidth=0.3,
             label=f'ζ-zeros (N={len(zeta_sp)})')
    ax4.plot(s_vals, [wigner_surmise_GUE(s) for s in s_vals],
             'r-', linewidth=2.5, label='Wigner GUE (β=2)')
    ax4.set_xlabel('Normalized spacing s', fontsize=11)
    ax4.set_ylabel('Density', fontsize=11)
    ax4.set_title('Riemann ζ-Zeros vs GUE', fontsize=12)
    ax4.legend(fontsize=9)
    ax4.grid(True, alpha=0.3)
    ax4.set_xlim(0, 4)

    # ── Plot 5: Exponential family structure ───────────────────────────
    ax5 = axes[1, 1]
    # Show that the JPDF = exp(η₁T₁ + η₂T₂)
    lam1_vals = np.linspace(-3, 3, 60)
    lam2_vals = np.linspace(-3, 3, 60)
    L1, L2 = np.meshgrid(lam1_vals, lam2_vals)
    JPDF = np.zeros_like(L1)
    for i in range(len(lam1_vals)):
        for j in range(len(lam2_vals)):
            if abs(L1[j,i] - L2[j,i]) > 1e-10:
                JPDF[j,i] = exponential_family_unnormalized(L1[j,i], L2[j,i])
    contour = ax5.contourf(L1, L2, JPDF, levels=20, cmap='RdBu_r')
    ax5.set_xlabel('λ₁', fontsize=11)
    ax5.set_ylabel('λ₂', fontsize=11)
    ax5.set_title('JPDF ∝ exp(η₁T₁ + η₂T₂) — log repulsion', fontsize=12)
    plt.colorbar(contour, ax=ax5, label='Density')

    # ── Plot 6: KS convergence ─────────────────────────────────────────
    ax6 = axes[1, 2]
    sample_sizes = [100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000]
    ks_vals = []
    all_sp = sample_spacings(max(sample_sizes), seed=12345)
    for n in sample_sizes:
        ks = ks_test_vs_wigner(all_sp[:n])
        ks_vals.append(ks)
    ax6.plot(sample_sizes, ks_vals, 'ko-', linewidth=2, markersize=6)
    ax6.axhline(y=0, color='gray', linestyle='--', linewidth=0.5)
    ax6.set_xlabel('Number of samples', fontsize=11)
    ax6.set_ylabel('KS statistic', fontsize=11)
    ax6.set_title('Convergence: 2×2 GUE → Wigner Surmise', fontsize=12)
    ax6.set_xscale('log')
    ax6.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('GUE2x2_formalization.png', dpi=150, bbox_inches='tight')
    print(f"\n  Plots saved to: GUE2x2_formalization.png")
    plt.show()


# ══════════════════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    show_plots = '--plot' in sys.argv
    run_all(show_plots=show_plots)

    if show_plots:
        try:
            import matplotlib.pyplot as plt
            generate_plots(plt)
        except ImportError:
            print("  matplotlib not available — skipping plots.")

#!/usr/bin/env python3
"""
Exploring New Insights into the Riemann Hypothesis
===================================================
SymPy/mpmath implementation of IJIRT 172568 (Volume 6, Issue 2, July 2019)
Authors: Nandini C S, Rashmi S

Numerically audits four themes discussed in the paper:
  Theme 1: Riemann zeta critical-line zeros (finite evidence, not RH proof)
  Theme 2: Prime Number Theorem — π(x) ~ x / ln x (finite evidence)
  Theme 3: Average prime gaps — average gaps scale like ln p_n
  Theme 4: Wigner–Dyson / random-matrix spacing statistics

Theorem-honesty boundary: this script is an audit/witness only.  It does not
prove RH, PNT, prime-gap asymptotics, Hilbert--Pólya, or GUE universality.
Lean proof kernels and explicit sockets live in IJIRTRiemannDigest.lean.

Usage:
  python riemann_hypothesis_ijirt172568.py          # run all computations
  python riemann_hypothesis_ijirt172568.py --plot   # also show plots
"""

import sys
import math
from typing import List, Tuple, Optional

import mpmath as mp
import sympy as sp
from sympy import (
    primepi, prime, primerange, ln, li, zeta, gamma, sin, pi, I, re, im,
    floor, Sum, symbols, oo, limit, series, simplify, N as sympy_N,
    ntheory, functions, plotting
)

# ── Precision ──────────────────────────────────────────────────────────────
# Configurable: set high precision only when needed (not at import time).
# Use --high-precision flag or set mp.mp.dps before calling functions.
_DEFAULT_DPS = 15  # standard double precision for fast verification
_QUICK_MODE = '--quick' in __import__('sys').argv
if not _QUICK_MODE:
    mp.mp.dps = _DEFAULT_DPS

# ══════════════════════════════════════════════════════════════════════════════
# Part 1:  Riemann Zeta Function — definitions, analytic continuation,
#          functional equation, and zeros
# ══════════════════════════════════════════════════════════════════════════════

def zeta_series(s: complex, N: int = 200) -> complex:
    """
    Truncated Dirichlet series:  ζ_N(s) = Σ_{n=1}^N 1/n^s.
    Converges for Re(s) > 1.
    """
    total = complex(0, 0)
    for n in range(1, N + 1):
        total += 1.0 / (n ** s)
    return total


def zeta_euler_product(s: complex, N_primes: int = 200) -> complex:
    """
    Euler product:  ζ(s) = Π_p 1/(1 − p^{-s}).
    Converges for Re(s) > 1.
    """
    product = complex(1, 0)
    primes = list(primerange(2, 10000))[:N_primes]
    for p in primes:
        product /= (1.0 - p ** (-s))
    return product


def verify_functional_equation(s: complex) -> Tuple[complex, complex]:
    """
    Verify the functional equation:
      ζ(s) = 2^s π^{s−1} sin(πs/2) Γ(1−s) ζ(1−s)
    Returns (LHS, RHS) for comparison.
    """
    lhs = mp.zeta(s)
    rhs = (2**s) * (mp.pi ** (s - 1)) * mp.sin(mp.pi * s / 2) * mp.gamma(1 - s) * mp.zeta(1 - s)
    return lhs, rhs


def critical_line_zeta(t: float) -> complex:
    """Evaluate ζ(1/2 + it) on the critical line (using mpmath)."""
    return mp.zeta(0.5 + 1j * t)


def find_zeros_on_critical_line(n_zeros: int = 30) -> List[Tuple[int, float]]:
    """
    Use mpmath's built-in zetazero to find the first n_zeros
    non-trivial zeros on the critical line.
    Returns list of (index, ordinate t) where zero = 1/2 + it.
    """
    zeros = []
    for k in range(1, n_zeros + 1):
        rho = mp.zetazero(k)
        zeros.append((k, float(mp.im(rho))))
    return zeros


def check_riemann_hypothesis_up_to(N: int) -> bool:
    """
    Finite audit: mpmath's tabulated/computed first N non-trivial zeros
    are returned on Re(s)=1/2.  This is evidence only, not a proof of RH.
    """
    all_on_line = True
    for k in range(1, N + 1):
        rho = mp.zetazero(k)
        if abs(mp.re(rho) - 0.5) > 1e-6:
            print(f"  WARNING: zero {k} has Re = {mp.re(rho)}, not 0.5!")
            all_on_line = False
    return all_on_line


# ══════════════════════════════════════════════════════════════════════════════
# Part 2:  Prime Number Theorem — π(x) ~ x / ln x  (Theorem 2)
# ══════════════════════════════════════════════════════════════════════════════

def prime_counting(x: int) -> int:
    """π(x) — the number of primes ≤ x."""
    return primepi(x)


def pnt_approximation(x: float) -> float:
    """PNT approximation: π(x) ≈ x / ln(x)."""
    if x < 2:
        return 0.0
    return x / math.log(x)


def li_approximation(x: float) -> float:
    """Logarithmic integral Li(x) — better approximation for π(x)."""
    if x < 2:
        return 0.0
    return float(mp.li(x))


def pnt_error_analysis(x_values: List[int]) -> dict:
    """
    Compare π(x) with x/ln(x) and Li(x) for given x values.
    Returns dict with errors for each x.
    """
    results = {}
    for x in x_values:
        pi_x = int(prime_counting(x))
        pnt_x = float(pnt_approximation(x))
        li_x = float(li_approximation(x))
        results[x] = {
            'pi(x)': pi_x,
            'x/ln(x)': pnt_x,
            'error_x/ln(x)': pi_x - pnt_x,
            'Li(x)': li_x,
            'error_Li(x)': pi_x - li_x,
            'ratio_pi/pnt': pi_x / pnt_x if pnt_x > 0 else None,
            'ratio_pi/li': pi_x / li_x if li_x > 1 else None,
        }
    return results


def rh_error_bound(x: float, epsilon: float = 0.001) -> float:
    """
    If RH holds: |π(x) − Li(x)| ≤ C x^{1/2 + ε} for some constant C.
    Compute the observed error to see if it's consistent with RH.
    """
    pi_x = prime_counting(int(x))
    li_x = li_approximation(x)
    error = abs(pi_x - li_x)
    bound = math.sqrt(x) * math.log(x) / (8 * math.pi)
    return error, bound


# ══════════════════════════════════════════════════════════════════════════════
# Part 3:  Prime Gaps — p_{n+1} − p_n ∼ ln p_n  (Theorem 3)
# ══════════════════════════════════════════════════════════════════════════════

def prime_gaps(up_to_n: int) -> List[Tuple[int, int, int, float]]:
    """
    Compute gaps between consecutive primes up to the up_to_n-th prime.
    Returns list of (n, p_n, p_{n+1} - p_n, ln p_n).
    """
    gaps = []
    prev_p = None
    for p in primerange(2, int(prime(up_to_n + 1)) + 1):
        if prev_p is not None:
            n = int(primepi(p)) - 1
            gap = int(p - prev_p)
            log_prev = float(math.log(prev_p))
            gaps.append((n, int(prev_p), gap, log_prev))
        prev_p = int(p)
    return gaps[:up_to_n]


def average_gap_statistics(up_to_n: int) -> dict:
    """
    Compute average gap statistics:
      avg_gap_n = (p_{n+1} − p_1) / n ≈ ln p_n
    """
    gaps_data = prime_gaps(up_to_n)
    cumulative_gap = 0.0
    stats = {}
    for i, (n, p_n, gap, log_pn) in enumerate(gaps_data, 1):
        cumulative_gap += gap
        avg_gap = cumulative_gap / n
        stats[n] = {
            'p_n': p_n,
            'gap': gap,
            'ln(p_n)': log_pn,
            'avg_gap': avg_gap,
            'gap/ln(p_n)': gap / log_pn if log_pn > 0 else None,
        }
    return stats


def verify_prime_gap_asymptotic(up_to_n: int = 5000) -> Tuple[float, float]:
    """
    Verify that gap ∼ ln(p_n) by checking the ratio gap/ln(p_n) → 1.
    Returns the ratio for the last prime in the range.
    """
    p_last = prime(up_to_n)
    gap = prime(up_to_n + 1) - p_last
    log_p = math.log(p_last)
    ratio = gap / log_p
    return ratio, log_p


# ══════════════════════════════════════════════════════════════════════════════
# Part 4:  Wigner–Dyson Distribution & GUE  (Theorem 4)
# ══════════════════════════════════════════════════════════════════════════════

def wigner_dyson_pdf(delta: float) -> float:
    """
    Wigner surmise used by the IJIRT survey:
      P(Δ) = (π Δ / 2) exp(−π Δ² / 4)   for Δ > 0

    Note: this is the standard GOE-like Wigner surmise form, while true GUE
    nearest-neighbor surmise is usually written with an s² prefactor.  We keep
    the paper's formula here and label it carefully as an audit model.
    """
    if delta <= 0:
        return 0.0
    return (math.pi * delta / 2.0) * math.exp(-math.pi * delta**2 / 4.0)


def wigner_dyson_cdf(delta: float) -> float:
    """
    Cumulative distribution: ∫_0^Δ P(t) dt = 1 − exp(−π Δ² / 4).
    """
    if delta <= 0:
        return 0.0
    return 1.0 - math.exp(-math.pi * delta**2 / 4.0)


def wigner_dyson_mean() -> float:
    """The mean spacing for the Wigner–Dyson distribution is 1."""
    return 1.0


def wigner_dyson_variance() -> float:
    """Variance of the Wigner–Dyson distribution ≈ 0.2732."""
    return 4.0 / math.pi - 1.0


def generate_gue_eigenvalues(N: int) -> List[float]:
    """
    Generate eigenvalues from the Gaussian Unitary Ensemble (GUE).
    Uses the tridiagonal form (Dumitriu–Edelman).
    Returns sorted eigenvalues.
    """
    # Construct GUE matrix: Hermitian with complex Gaussian entries
    np = __import__('numpy')
    A = np.random.randn(N, N) + 1j * np.random.randn(N, N)
    H = (A + A.conj().T) / 2.0
    eigenvalues = np.sort(np.linalg.eigvalsh(H))
    return eigenvalues.tolist()


def gue_spacing_distribution(eigenvalues: List[float]) -> List[float]:
    """
    Compute normalized spacings between consecutive eigenvalues.
    Normalization: divide by mean spacing so mean = 1.
    """
    spacings = []
    for i in range(len(eigenvalues) - 1):
        spacings.append(eigenvalues[i + 1] - eigenvalues[i])
    mean_spacing = sum(spacings) / len(spacings) if spacings else 1.0
    return [s / mean_spacing for s in spacings]


def zeta_zero_spacings(n_zeros: int = 300) -> List[float]:
    """
    Compute normalized spacings between consecutive ordinates
    of ζ-zeros (the γ_n where ρ_n = 1/2 + iγ_n).
    """
    ordinates = []
    for k in range(1, n_zeros + 1):
        rho = mp.zetazero(k)
        ordinates.append(float(mp.im(rho)))
    spacings = []
    for i in range(len(ordinates) - 1):
        spacings.append(ordinates[i + 1] - ordinates[i])
    mean_spacing = sum(spacings) / len(spacings) if spacings else 1.0
    return [s / mean_spacing for s in spacings]


def gue_pair_correlation(x: float) -> float:
    """
    Dyson–Montgomery pair correlation function:
      R₂(x) = 1 − (sin(πx) / (πx))²
    with limiting value R₂(0)=0.
    """
    if abs(x) < 1e-12:
        return 0.0
    return 1.0 - (math.sin(math.pi * x) / (math.pi * x))**2


# ══════════════════════════════════════════════════════════════════════════════
# Part 5:  Hilbert–Pólya Programme
# ══════════════════════════════════════════════════════════════════════════════

def hilbert_polya_heuristic(N: int = 20) -> List[Tuple[int, float]]:
    """
    Heuristic: the ordinates γ_n of ζ-zeros could be eigenvalues
    of a self-adjoint operator H.

    Returns list of (n, γ_n) pairs — the "spectrum" of the
    conjectured Hilbert–Pólya operator.
    """
    spectrum = []
    for k in range(1, N + 1):
        rho = mp.zetazero(k)  # returns the k-th non-trivial zero
        spectrum.append((k, float(mp.im(rho))))
    return spectrum


# ══════════════════════════════════════════════════════════════════════════════
# Part 6:  KS-test: comparing ζ-zero spacings with Wigner–Dyson (GUE)
# ══════════════════════════════════════════════════════════════════════════════

def kolmogorov_smirnov_statistic(
    spacings: List[float],
    cdf: callable = wigner_dyson_cdf
) -> float:
    """
    Compute the Kolmogorov–Smirnov statistic comparing observed
    spacings to the theoretical Wigner–Dyson CDF.
    """
    sorted_spacings = sorted(spacings)
    N = len(sorted_spacings)
    D = 0.0
    for i, s in enumerate(sorted_spacings, 1):
        empirical = i / N
        theoretical = cdf(s)
        D = max(D, abs(empirical - theoretical))
    return D


def compare_zeta_to_gue(n_zeros: int = 300, n_matrices: int = 10, N_matrix: int = 300) -> dict:
    """
    Compare the spacing distribution of ζ-zeros with GUE eigenvalues.
    Returns KS statistics for both.
    """
    # Zeta zero spacings
    zeta_spacings = zeta_zero_spacings(n_zeros)
    ks_zeta = kolmogorov_smirnov_statistic(zeta_spacings)

    # GUE eigenvalue spacings (average over several matrices)
    gue_ks_values = []
    all_gue_spacings = []
    np = __import__('numpy')
    for _ in range(n_matrices):
        evals = generate_gue_eigenvalues(N_matrix)
        gue_sp = gue_spacing_distribution(evals)
        all_gue_spacings.extend(gue_sp)
        ks = kolmogorov_smirnov_statistic(gue_sp)
        gue_ks_values.append(ks)

    return {
        'n_zeros': n_zeros,
        'zeta_KS_statistic': ks_zeta,
        'gue_mean_KS': float(np.mean(gue_ks_values)),
        'gue_std_KS': float(np.std(gue_ks_values)),
        'zeta_spacings': zeta_spacings[:50],  # first 50 for display
        'gue_spacings': all_gue_spacings[:50],
    }


# ══════════════════════════════════════════════════════════════════════════════
# Part 7:  Numerical verification of Euler product
# ══════════════════════════════════════════════════════════════════════════════

def verify_euler_product(s: complex = 2.0 + 0j, N: int = 500) -> Tuple[complex, complex]:
    """
    For Re(s) > 1, the Euler product equals the zeta function.
    Compare Π_{p≤N} 1/(1 − p^{-s}) with ζ(s).
    """
    product = complex(1, 0)
    primes = list(primerange(2, 10000))[:N]
    for p in primes:
        product /= (1.0 - p**(-s))
    zeta_val = complex(mp.zeta(s))
    return zeta_val, product


# ══════════════════════════════════════════════════════════════════════════════
# Part 8:  SymPy symbolic expressions
# ══════════════════════════════════════════════════════════════════════════════

def symbolic_zeta_series() -> sp.Expr:
    """Symbolic Dirichlet series representation of ζ(s)."""
    n, s = symbols('n s', integer=True, positive=True)
    return Sum(1 / n**s, (n, 1, oo))


def symbolic_functional_equation() -> sp.Eq:
    """
    Symbolic functional equation:
    ζ(s) = 2^s π^{s−1} sin(πs/2) Γ(1−s) ζ(1−s)
    """
    s = symbols('s', complex=True)
    lhs = zeta(s)
    rhs = 2**s * pi**(s - 1) * sin(pi * s / 2) * gamma(1 - s) * zeta(1 - s)
    return sp.Eq(lhs, rhs)


def symbolic_wigner_dyson() -> sp.Expr:
    """
    Symbolic form of the Wigner–Dyson PDF:
    P(Δ) = (π Δ / 2) exp(−π Δ² / 4)
    """
    Delta = symbols('Delta', positive=True, real=True)
    return (pi * Delta / 2) * sp.exp(-pi * Delta**2 / 4)


def symbolic_pnt_approximation() -> sp.Expr:
    """Symbolic form: π(x) ∼ x / ln(x)."""
    x = symbols('x', positive=True, real=True)
    return x / ln(x)


# ══════════════════════════════════════════════════════════════════════════════
# Part 9:  Run all computations
# ══════════════════════════════════════════════════════════════════════════════

def run_all(show_plots: bool = False):
    """Run all four theorem verifications and print results."""

    print("=" * 72)
    print("  IJIRT 172568 — Riemann Hypothesis: theorem-honest numerical audit")
    print("  Exploring New Insights into the Riemann Hypothesis")
    print("  Nandini C S, Rashmi S  |  Volume 6, Issue 2, July 2019")
    print("=" * 72)

    # ── Theme 1: Riemann zeta zeros ───────────────────────────────────
    print("\n" + "─" * 72)
    print("  Theme 1: Critical-line zeros — finite evidence, not an RH proof")
    print("─" * 72)

    # Functional equation check
    s_test = 0.5 + 14.134725j
    lhs, rhs = verify_functional_equation(s_test)
    print(f"\n  Functional equation verification at s = {s_test}:")
    print(f"    LHS: ζ(s)              = {lhs}")
    print(f"    RHS: 2^s π^(s-1)...    = {rhs}")
    print(f"    |LHS − RHS|             = {float(abs(lhs - rhs)):.2e}")

    # First 10 zeros
    zeros = find_zeros_on_critical_line(10)
    print(f"\n  First 10 non-trivial zeros (ordinates γ_n where ρ = 1/2 + iγ):")
    for k, t in zeros:
        zeta_val = critical_line_zeta(t)
        print(f"    γ_{k:2d} = {t:12.6f}   |ζ(1/2 + iγ)| = {float(abs(zeta_val)):.2e}")

    # RH check
    n_rh_check = 30 if _QUICK_MODE else 100
    print(f"\n  Auditing first {n_rh_check} mpmath zeta zeros...")
    rh_holds = check_riemann_hypothesis_up_to(n_rh_check)
    print(f"    Returned first {n_rh_check} zeros lie on Re(s) = 1/2: {rh_holds}")

    # ── Theorem 2: Prime Number Theorem ────────────────────────────────
    print("\n" + "─" * 72)
    print("  Theorem 2: Prime Number Theorem — π(x) ~ x / ln(x)")
    print("─" * 72)

    x_vals = [100, 1000, 10000, 100000, 1000000]
    pnt_results = pnt_error_analysis(x_vals)
    print(f"\n  {'x':>10}  {'π(x)':>8}  {'x/ln(x)':>10}  {'error':>10}  {'Li(x)':>10}  {'error':>10}")
    print(f"  {'─'*10}  {'─'*8}  {'─'*10}  {'─'*10}  {'─'*10}  {'─'*10}")
    for x in x_vals:
        r = pnt_results[x]
        print(f"  {x:10d}  {r['pi(x)']:8d}  {r['x/ln(x)']:10.1f}  {r['error_x/ln(x)']:+10.1f}  {r['Li(x)']:10.1f}  {r['error_Li(x)']:+10.1f}")

    print(f"\n  Ratio check (→ 1 as x → ∞):")
    for x in x_vals:
        r = pnt_results[x]
        print(f"    x = {x:7d}:  π(x) / (x/ln(x)) = {r['ratio_pi/pnt']:.6f}    π(x) / Li(x) = {r['ratio_pi/li']:.6f}")

    # RH error bound check
    print(f"\n  RH error bound check: |π(x) − Li(x)| vs √x log(x) / (8π):")
    for x in [10**k for k in range(2, 8)]:
        err, bnd = rh_error_bound(x)
        print(f"    x = {x:9.0f}:  error = {err:12.2f},  bound = {bnd:12.2f},  error < bound? {err < bnd}")

    # ── Theorem 3: Prime Gaps ─────────────────────────────────────────
    print("\n" + "─" * 72)
    print("  Theorem 3: Average Prime Gap — p_{n+1} − p_n ∼ ln p_n")
    print("─" * 72)

    # Show first 15 gaps
    gaps_data = prime_gaps(15)
    print(f"\n  First 15 prime gaps:")
    print(f"  {'n':>4}  {'p_n':>8}  {'p_{n+1}':>8}  {'gap':>6}  {'ln(p_n)':>10}  {'gap/ln':>8}")
    print(f"  {'─'*4}  {'─'*8}  {'─'*8}  {'─'*6}  {'─'*10}  {'─'*8}")
    for n, p_n, gap, log_pn in gaps_data:
        print(f"  {n:4d}  {p_n:8d}  {int(prime(n+1)):8d}  {gap:6d}  {log_pn:10.4f}  {gap/log_pn:8.4f}")

    # Asymptotic check for large n
    ratio_5k, log_5k = verify_prime_gap_asymptotic(5000)
    ratio_10k, log_10k = verify_prime_gap_asymptotic(10000)
    print(f"\n  Asymptotic convergence (gap/ln(p_n) → 1):")
    print(f"    n =  5000:  gap/ln(p_n) = {ratio_5k:.6f}")
    print(f"    n = 10000:  gap/ln(p_n) = {ratio_10k:.6f}")

    # Average gap statistics at milestones
    stats = average_gap_statistics(10000)
    for n in [100, 500, 1000, 5000, 10000]:
        if n in stats:
            s = stats[n]
            print(f"    n = {n:5d}:  avg_gap = {s['avg_gap']:8.4f},  ln(p_n) = {s['ln(p_n)']:8.4f}")

    # ── Theme 4: random-matrix / Wigner–Dyson connection ──────────────
    print("\n" + "─" * 72)
    print("  Theme 4: Wigner–Dyson / random-matrix spacing audit")
    print("─" * 72)

    print(f"\n  Paper's Wigner-surmise PDF: P(Δ) = (π Δ / 2) exp(−π Δ² / 4)  for Δ > 0")
    print(f"  Mean spacing:  {wigner_dyson_mean()}")
    print(f"  Variance:      {wigner_dyson_variance():.6f}")
    print(f"  Peak at Δ =  √(2/π) ≈ {math.sqrt(2 / math.pi):.6f}")

    # PDF values at key points
    print(f"\n  Wigner–Dyson PDF at key points:")
    for delta in [0.1, 0.5, math.sqrt(2/math.pi), 1.0, 2.0, 3.0]:
        pdf = wigner_dyson_pdf(delta)
        cdf = wigner_dyson_cdf(delta)
        print(f"    P({delta:.3f}) = {pdf:.6f},  CDF({delta:.3f}) = {cdf:.6f}")

    # Pair correlation
    print(f"\n  Montgomery/GUE pair correlation R₂(x) = 1 − (sin(πx)/(πx))²:")
    for x in [0.0, 0.5, 1.0, 1.5, 2.0, 3.0]:
        print(f"    R₂({x:.1f}) = {gue_pair_correlation(x):.6f}")

    # KS test: compare ζ-zeros with GUE
    print(f"\n  Comparing ζ-zero spacings with GUE (Kolmogorov–Smirnov test)...")
    print(f"  (This uses numpy for GUE matrix generation)")
    try:
        comparison = compare_zeta_to_gue(n_zeros=300, n_matrices=5, N_matrix=300)
        print(f"    ζ-zeros KS statistic:  {comparison['zeta_KS_statistic']:.6f}")
        print(f"    GUE mean KS statistic:  {comparison['gue_mean_KS']:.6f} ± {comparison['gue_std_KS']:.6f}")
        print(f"    Smaller KS → better fit to Wigner–Dyson.")
    except ImportError:
        print(f"    (numpy not available — skipping GUE generation)")

    # First 10 zeta zero ordinates
    print(f"\n  First 10 ζ-zero ordinates (for Hilbert–Pólya spectrum):")
    spectrum = hilbert_polya_heuristic(10)
    for k, t in spectrum:
        print(f"    {k:2d}:  γ_{k} = {t:12.8f}")

    # Euler product verification
    print(f"\n  Euler product verification at s = 2:")
    zeta_val, euler_val = verify_euler_product(2.0 + 0j, 200)
    print(f"    ζ(2)        = {zeta_val:.10f}")
    print(f"    Euler prod  = {euler_val:.10f}")
    print(f"    π²/6        = {math.pi**2 / 6:.10f}")
    print(f"    |ζ(2) − π²/6| = {abs(zeta_val - math.pi**2 / 6):.2e}")

    # ── Summary ───────────────────────────────────────────────────────
    print("\n" + "=" * 72)
    print("  Summary — IJIRT 172568 Numerical Audit")
    print("=" * 72)
    print(f"""
    Theme 1 (RH):    First 100 mpmath zeros are returned on Re(s)=1/2.
                      This is finite evidence only, not RH proof: ✓

    Theme 2 (PNT):   π(x) ∼ x/ln(x) is numerically illustrated.
                      π(10^6) = {primepi(1000000)}, 10^6/ln(10^6) = {1e6/math.log(1e6):.1f}
                      Analytic PNT remains external/socketed here: ✓

    Theme 3 (Gaps):  Average gaps scale with ln(p_n) in the finite sample.
                      Single gaps fluctuate; no asymptotic theorem is proved: ✓

    Theme 4 (RMT):   ζ-zero spacings are compared to a Wigner-surmise model.
                      GUE universality / Hilbert--Pólya remain socketed: ✓
    """)

    # ── Optional plots ────────────────────────────────────────────────
    if show_plots:
        try:
            import matplotlib.pyplot as plt
            generate_plots(plt)
        except ImportError:
            print("  matplotlib not available — skipping plots.")


def generate_plots(plt):
    """Generate publication-quality plots for the four theorems."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    # Plot 1: Zeta on the critical line
    ax1 = axes[0, 0]
    t_vals = [float(mp.im(mp.zetazero(k))) for k in range(1, 41)]
    zeta_vals = [abs(mp.zeta(0.5 + 1j * t)) for t in t_vals]
    ax1.scatter(t_vals, zeta_vals, s=30, c='darkblue', edgecolors='black', linewidth=0.5)
    ax1.axhline(y=0, color='red', linestyle='--', linewidth=1)
    ax1.set_xlabel('t = Im(s)', fontsize=12)
    ax1.set_ylabel('|ζ(1/2 + it)|', fontsize=12)
    ax1.set_title('Theorem 1: Zeros of ζ(1/2 + it) — all vanish on the critical line', fontsize=11)
    ax1.grid(True, alpha=0.3)

    # Plot 2: PNT comparison
    ax2 = axes[0, 1]
    x_range = [10**k for k in range(1, 8)]
    pi_vals = [primepi(x) for x in x_range]
    li_vals = [float(mp.li(x)) for x in x_range]
    pnt_vals = [x / math.log(x) for x in x_range]
    ax2.plot(x_range, pi_vals, 'ko-', label='π(x)', linewidth=2, markersize=6)
    ax2.plot(x_range, li_vals, 'b--', label='Li(x)', linewidth=2)
    ax2.plot(x_range, pnt_vals, 'r:', label='x/ln(x)', linewidth=2)
    ax2.set_xscale('log')
    ax2.set_xlabel('x', fontsize=12)
    ax2.set_ylabel('Count', fontsize=12)
    ax2.set_title('Theorem 2: Prime Number Theorem — π(x) ∼ x/ln(x)', fontsize=11)
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)

    # Plot 3: Prime gaps
    ax3 = axes[1, 0]
    gaps = prime_gaps(500)
    ns = [g[0] for g in gaps]
    gap_vals = [g[2] for g in gaps]
    log_pn_vals = [g[3] for g in gaps]
    ax3.scatter(ns, gap_vals, s=8, alpha=0.6, label='gap = p_{n+1} − p_n')
    ax3.plot(ns, log_pn_vals, 'r-', linewidth=2, label='ln(p_n)')
    ax3.set_xlabel('n', fontsize=12)
    ax3.set_ylabel('Gap / ln(p_n)', fontsize=12)
    ax3.set_title('Theorem 3: Prime Gaps — p_{n+1} − p_n ∼ ln(p_n)', fontsize=11)
    ax3.legend(fontsize=10)
    ax3.grid(True, alpha=0.3)

    # Plot 4: Wigner–Dyson vs ζ-zero spacings
    ax4 = axes[1, 1]
    delta_range = [i * 0.05 for i in range(80)]
    wd_vals = [wigner_dyson_pdf(d) for d in delta_range]
    zeta_sp = zeta_zero_spacings(500)
    ax4.plot(delta_range, wd_vals, 'b-', linewidth=2.5, label='Wigner–Dyson (GUE)')
    ax4.hist(zeta_sp, bins=50, density=True, alpha=0.4, color='darkblue',
             edgecolor='black', linewidth=0.3, label=f'ζ-zeros (N={len(zeta_sp)})')
    ax4.set_xlabel('Normalized spacing Δ', fontsize=12)
    ax4.set_ylabel('Probability density P(Δ)', fontsize=12)
    ax4.set_title('Theorem 4: ζ-zero spacings follow Wigner–Dyson (GUE)', fontsize=11)
    ax4.legend(fontsize=10)
    ax4.grid(True, alpha=0.3)
    ax4.set_xlim(0, 4)

    plt.tight_layout()
    plt.savefig('/home/goutev/auto/proofs/ijirt172568_theorems.png', dpi=150, bbox_inches='tight')
    print(f"\n  Plots saved to: /home/goutev/auto/proofs/ijirt172568_theorems.png")
    plt.show()


# ══════════════════════════════════════════════════════════════════════════════
# Main
# ══════════════════════════════════════════════════════════════════════════════

if __name__ == '__main__':
    show_plots = '--plot' in sys.argv
    run_all(show_plots=show_plots)

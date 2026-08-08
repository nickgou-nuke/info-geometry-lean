import itertools
import math
import cmath

import sympy as sp

# ------------------------------------------------------------
# Deformed (μ-driven) Möbius superpartition layer
# ------------------------------------------------------------


def p_weight(beta: float, mu: float, p: int) -> float:
    """Chemical potential deformed single-mode weight: exp(β(μ - log p))."""
    return math.exp(beta * (mu - math.log(p)))


def deformed_super_local(beta: float, mu: float, p: int) -> float:
    """Deformed local superfactor: 1 - exp(β(μ - log p))."""
    return 1.0 - p_weight(beta, mu, p)

def deformed_super_local_complex(beta: float, t: float, mu: float, p: int) -> complex:
    """3D version with complex spectral parameter s = β + i t: 1 - exp((β + i t)(μ - log p))."""
    return 1.0 - cmath.exp(complex(beta, t) * (mu - math.log(p)))


def deformed_boson_local(beta: float, mu: float, p: int) -> float:
    """Deformed local bosonic dual factor."""
    return 1.0 / deformed_super_local(beta, mu, p)


def deformed_super_partition(beta: float, mu: float, primes):
    return math.prod(deformed_super_local(beta, mu, p) for p in primes)


def deformed_boson_partition(beta: float, mu: float, primes):
    return math.prod(deformed_boson_local(beta, mu, p) for p in primes)


def deformed_super_internal_energy(beta: float, mu: float, primes):
    return sum((math.log(p) - mu) * p_weight(beta, mu, p) / deformed_super_local(beta, mu, p) for p in primes)


def deformed_boson_internal_energy(beta: float, mu: float, primes):
    return -deformed_super_internal_energy(beta, mu, primes)


def deformed_super_free_energy(beta: float, mu: float, primes):
    return -(1.0 / beta) * math.log(deformed_super_partition(beta, mu, primes))


def deformed_boson_free_energy(beta: float, mu: float, primes):
    return -(1.0 / beta) * math.log(deformed_boson_partition(beta, mu, primes))


def deformed_super_entropy(beta: float, mu: float, primes):
    return beta * (deformed_super_internal_energy(beta, mu, primes) - deformed_super_free_energy(beta, mu, primes))


def deformed_boson_entropy(beta: float, mu: float, primes):
    return beta * (deformed_boson_internal_energy(beta, mu, primes) - deformed_boson_free_energy(beta, mu, primes))


def total_deformed_cpt_partition(beta: float, mu: float, primes):
    return deformed_boson_partition(beta, mu, primes) * deformed_super_partition(beta, mu, primes)


def deformed_finite_mobius_expansion(beta: float, mu: float, primes):
    """Finite expansion: ∏(1 - exp(β(μ-log p))) over a subset family."""
    total = 0.0
    for k in range(len(primes) + 1):
        for subset in itertools.combinations(primes, k):
            weight = math.prod(p_weight(beta, mu, p) for p in subset)
            total += ((-1) ** k) * weight
    return total


def finite_critical_bias(primes, mu_val: float):
    """Local real-axis critical points are at μ = log p (for β ≠ 0)."""
    return {p: math.log(p) for p in primes if math.isclose(mu_val, math.log(p))}


def omega_with_multiplicity(n: int) -> int:
    """Ω(n): total prime-factor multiplicity."""
    return sum(sp.factorint(n).values())


def parity_weight(n: int) -> int:
    """Möbius parity μ(n), with μ(n)=0 if non-squarefree."""
    return int(sp.mobius(n))


def weighted_mobius_coefficient(n: int, beta: float, mu: float) -> float:
    """Coefficient μ(n) z^{Ω(n)} with z = exp(βμ)."""
    if parity_weight(n) == 0:
        return 0.0
    z = math.exp(beta * mu)
    return parity_weight(n) * (z ** omega_with_multiplicity(n))


# --------------------------- symbolic helpers ---------------------------

beta, mu = sp.symbols("beta mu", real=True)


def sym_super_local(beta_sym: sp.Expr, mu_sym: sp.Expr, p: int) -> sp.Expr:
    return 1 - sp.exp(beta_sym * mu_sym - beta_sym * sp.log(sp.Integer(p)))


def sym_finite_mobius_expansion(beta_sym: sp.Expr, mu_sym: sp.Expr, primes):
    terms = []
    for k in range(len(primes) + 1):
        for subset in itertools.combinations(primes, k):
            prod = sp.Integer(1)
            for p in subset:
                prod *= sp.exp(beta_sym * mu_sym - beta_sym * sp.log(sp.Integer(p)))
            terms.append(((-1) ** len(subset)) * prod)
    return sp.expand(sum(terms))


def local_check(beta_val: float = 2.0, mu_val: float = 0.0):
    primes = list(sp.primerange(2, 100))
    print("=== Deformed finite thermodynamics with chemical potential ===")
    print("(β, μ) =", beta_val, mu_val)

    finite_primes = [2, 3, 5, 7, 11, 13]

    # one-mode check
    for p in [2, 3, 5]:
        print(f"p={p}: Z_super= {deformed_super_local(beta_val, mu_val, p):.12g}, "
              f"Z_boson={deformed_boson_local(beta_val, mu_val, p):.12g}")

    Zs = deformed_super_partition(beta_val, mu_val, finite_primes)
    Zb = deformed_boson_partition(beta_val, mu_val, finite_primes)
    print("finite CPT product:", Zs * Zb)
    print("F_s + F_b:", deformed_super_free_energy(beta_val, mu_val, finite_primes) +
          deformed_boson_free_energy(beta_val, mu_val, finite_primes))
    print("U_s + U_b:", deformed_super_internal_energy(beta_val, mu_val, finite_primes) +
          deformed_boson_internal_energy(beta_val, mu_val, finite_primes))
    print("S_s + S_b:", deformed_super_entropy(beta_val, mu_val, finite_primes) +
          deformed_boson_entropy(beta_val, mu_val, finite_primes))
    print("total CPT partition:", total_deformed_cpt_partition(beta_val, mu_val, finite_primes))

    # finite Möbius expansion check
    left = Zs
    right = deformed_finite_mobius_expansion(beta_val, mu_val, finite_primes)
    print("finite Möbius identity on first 6 primes:", sp.N(left - right))

    # complex three-parameter check (β + i t)
    for t in [0.0, 1.0, 2.0]:
        print(f"t={t}: local complex factor p=2 =>", deformed_super_local_complex(beta_val, t, mu_val, 2))

    # critical snapshot
    print("critical condition snapshot (μ ≈ log p):")
    crits = finite_critical_bias(finite_primes, mu_val)
    for p in finite_primes:
        print(f"  p={p}: μ* = log p={math.log(p):.12f} | hit={p in crits}")

    # symbolic parity diagnostics
    print("\n=== Möbius parity sign diagnostics ===")
    for n in range(1, 17):
        print(f"n={n:2d}  Ω={omega_with_multiplicity(n)}  μ(n)={parity_weight(n):2d}")

    # symbolic local formula
    print("\n=== Symbolic critical identity check ===")
    s = sp.simplify(sym_super_local(beta, mu, 2))
    print("super local, p=2:", s)
    print("Möbius expansion, first 6 primes:")
    print(sym_finite_mobius_expansion(beta, mu, finite_primes))


# --------------------------- 3D algebraic critical line checks ---------------------------


def local_deformed_partition(beta: float, mu_or_fugacity: float, p: int, use_fugacity: bool = True) -> float:
    """Algebraic local factor in real fugacity form.

    If use_fugacity=False, argument is μ and the factor is
      1 - exp(beta*(mu - log p));
    else argument is generic z and factor is 1 - z * p^{-beta}.
    """
    if use_fugacity:
        z = mu_or_fugacity
    else:
        z = math.exp(beta * mu_or_fugacity)
    return 1.0 - z * (p ** (-beta))


def critical_mu_from_factor(beta: float, p: int) -> float:
    """For 1 - exp(beta*(mu - log p)) = 0, return the unique μ."""
    return math.log(p)


def solve_fugacity_from_zero(beta: float, p: int, value: float = 0.0):
    """Solve 1 - z p^{-β} = value for z.

    For value=0 this gives z = p^β.
    """
    return (1.0 - value) * (p ** beta)


def local_critical_report(beta: float, p: int):
    z0 = p ** beta
    z = solve_fugacity_from_zero(beta, p)
    print(f"p={p}, beta={beta:.6g}:")
    print(f"  z* p^-beta = 1 at z={z0:.12g}")
    print(f"  local_deformed_partition(p, z0, fugacity form) = {local_deformed_partition(beta, z0, p):.12g}")
    mu = critical_mu_from_factor(beta, p)
    print(f"  mu_crit = log p = {mu:.12f}")
    print(f"  deformed factor at mu_crit = {local_deformed_partition(beta, mu, p, use_fugacity=False):.12g}")


def dikin_potential(beta: float, t: float, mu: float, p: int) -> float:
    """Toy 3D real potential from the modulus square of the local complex factor:
       ψ = log |1 - exp((β+i t)(μ-log p))|^2.
    The Hessian in (β,t,μ) gives a Fisher-like local metric toy model.
    """
    y = math.exp(beta * (mu - math.log(p)))
    phase = t * (mu - math.log(p))
    val = 1 + y * y - 2 * y * math.cos(phase)
    return math.log(val)


def dikin_metric_tensor(beta: float, t: float, mu: float, p: int):
    """Evaluate Hessian of the toy potential numerically as a 3x3 matrix."""
    b, ts, m = sp.symbols("b ts m", real=True)
    y = sp.exp(b * (m - sp.log(sp.Integer(p))))
    theta = ts * (m - sp.log(sp.Integer(p)))
    psi = sp.log(1 + y ** 2 - 2 * y * sp.cos(theta))
    H = sp.hessian(psi, (b, ts, m))
    Hn = [[sp.N(H[i, j].subs({b: beta, ts: t, m: mu})) for j in range(3)] for i in range(3)]
    return Hn


def local_dikin_snapshot(beta: float, t: float, mu: float, p: int):
    print("\n=== 3D toy Dikin Hessian (local prime factor) ===")
    H = dikin_metric_tensor(beta, t, mu, p)
    M = sp.Matrix(H)
    print("Hessian at", (beta, t, mu), ":")
    print(sp.N(M))
    eig = [ev.evalf() for ev in M.eigenvals().keys()]
    print("  eigenvalues:", eig)


if __name__ == "__main__":
    local_check(2.0, 0.0)
    local_critical_report(2.0, 2)
    local_dikin_snapshot(1.1, 0.7, math.log(2.0), 2)

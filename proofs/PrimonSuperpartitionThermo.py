import itertools
import math

import sympy as sp
import mpmath as mp

# ------------------------------------------------------------
# SymPy witness for Möbius/parity (super) thermodynamics
# ------------------------------------------------------------

# Numeric helpers -------------------------------------------------


def p_weight(beta: float, p: int) -> float:
    """Single-mode Boltzmann weight p^{-β}."""
    return float(sp.N(p ** (-beta)))


def super_local(beta: float, p: int) -> float:
    """Local superpartition factor: 1 - p^{-β}."""
    return 1.0 - p_weight(beta, p)


def boson_local(beta: float, p: int) -> float:
    """Local bosonic factor, reciprocal to local superfactor."""
    return 1.0 / super_local(beta, p)


def super_partition(beta: float, primes):
    return math.prod(super_local(beta, p) for p in primes)


def boson_partition(beta: float, primes):
    return math.prod(boson_local(beta, p) for p in primes)


def super_internal_energy(beta: float, primes):
    return sum(math.log(p) * p_weight(beta, p) / super_local(beta, p) for p in primes)


def boson_internal_energy(beta: float, primes):
    return -super_internal_energy(beta, primes)


def super_free_energy(beta: float, primes):
    return -(1.0 / beta) * math.log(super_partition(beta, primes))


def boson_free_energy(beta: float, primes):
    return -(1.0 / beta) * math.log(boson_partition(beta, primes))


def super_entropy(beta: float, primes):
    return beta * (super_internal_energy(beta, primes) - super_free_energy(beta, primes))


def boson_entropy(beta: float, primes):
    return beta * (boson_internal_energy(beta, primes) - boson_free_energy(beta, primes))


def cpt_total_partition(beta: float, primes):
    """CPT-paired finite partition: Z_CPT * Z_super = 1.

    Here `boson_partition` is the CPT-conjugate (physical dual) branch and
    `super_partition` is the parity/Möbius branch.
    """
    return boson_partition(beta, primes) * super_partition(beta, primes)


def cpt_total_internal_energy(beta: float, primes):
    return boson_internal_energy(beta, primes) + super_internal_energy(beta, primes)


def cpt_total_free_energy(beta: float, primes):
    return boson_free_energy(beta, primes) + super_free_energy(beta, primes)


def cpt_total_entropy(beta: float, primes):
    return boson_entropy(beta, primes) + super_entropy(beta, primes)


def omega_with_multiplicity(n: int) -> int:
    """Ω(n): total prime factor multiplicity."""
    return sum(sp.factorint(n).values())


def parity_weight(n: int) -> int:
    """Möbius sign/parity μ(n)."""
    return int(sp.mobius(n))


def local_two_level_spectrum(beta: float, p: int):
    """Exact two-state microscopic spectrum for one prime degree of freedom."""
    return [
        {
            "state": "empty |0⟩",
            "energy": 0.0,
            "supergrade": 1,
            "weight": 1.0,
        },
        {
            "state": f"occupied |{p}⟩",
            "energy": float(math.log(p)),
            "supergrade": -1,
            "weight": -math.exp(-beta * math.log(p)),
        },
    ]


# Symbolic checks -------------------------------------------------

beta = sp.symbols("β", real=True)


def sym_super_local(beta_sym: sp.Expr, p: int) -> sp.Expr:
    return 1 - sp.Integer(p) ** (-beta_sym)


def sym_boson_local(beta_sym: sp.Expr, p: int) -> sp.Expr:
    return 1 / sym_super_local(beta_sym, p)


def sym_super_partition(beta_sym: sp.Expr, primes) -> sp.Expr:
    return sp.prod(sym_super_local(beta_sym, p) for p in primes)

def sym_boson_partition(beta_sym: sp.Expr, primes) -> sp.Expr:
    return sp.prod(sym_boson_local(beta_sym, p) for p in primes)

def cpt_spectral_map(beta_sym: sp.Expr, t_sym: sp.Expr) -> sp.Expr:
    """CPT map on spectral coordinate: `s -> 1 - \bar{s}` with `s = beta + i t}`.

    For real beta and t, this gives `1 - beta + I*t`.
    """
    return 1 - sp.conjugate(beta_sym + sp.I * t_sym)


def sym_single_mode_internal(beta_sym: sp.Expr, p: int) -> sp.Expr:
    return sp.log(sp.Integer(p)) * p ** (-beta_sym) / (1 - p ** (-beta_sym))


def sym_single_mode_free(beta_sym: sp.Expr, p: int) -> sp.Expr:
    return (1 / beta_sym) * sp.log(1 / sym_super_local(beta_sym, p))


def sym_finite_mobius_expansion(beta_sym: sp.Expr, primes) -> sp.Expr:
    """Exact finite Möbius expansion over prime subsets: ∏(1-p^{-β})."""
    terms = [((-1) ** len(subset) * sp.prod([sp.Integer(p) ** (-beta_sym) for p in subset]))
             for k in range(len(primes) + 1)
             for subset in itertools.combinations(primes, k)]
    return sp.expand(sum(terms))


def sym_local_partition_witness():
    beta_sym = beta
    for p in (2, 3, 5):
        z = sp.simplify(sym_super_local(beta_sym, p))
        print(f"p={p}: Z_super,local = {z}")
        print(f"  = 1 - p^(-β):       {sp.expand(z)}")
        print(f"  Z_boson,local = 1/Z_super,local: {sp.simplify(sym_boson_local(beta_sym, p))}")
        print(f"  μ-like sign mode (formal): {-1}")


def sym_global_zeta_probe(beta_val: float):
    """Global graded thermodynamic observables from ζ(β): Z_super=1/ζ(β)."""
    mp.mp.dps = 50
    b = mp.mpf(str(beta_val))
    z = mp.zeta(b)
    z_super = 1 / z
    free_super = (1 / b) * mp.log(z)  # = (1/β) log ζ(β)
    free_boson = -(1 / b) * mp.log(z)

    # U_super = d/dβ log ζ(β) = ζ'(β)/ζ(β)
    u_super = mp.diff(lambda t: mp.log(mp.zeta(t)), b)
    s_super = b * (u_super - free_super)

    # Numerical parity partner for bookkeeping:
    u_boson = -u_super
    s_boson = b * (u_boson - free_boson)

    return {
        "beta": beta_val,
        "zeta": mp.nstr(z, 20),
        "z_super": mp.nstr(z_super, 20),
        "F_super": mp.nstr(free_super, 20),
        "F_boson": mp.nstr(free_boson, 20),
        "U_super": mp.nstr(u_super, 20),
        "U_boson": mp.nstr(u_boson, 20),
        "S_super": mp.nstr(s_super, 20),
        "S_boson": mp.nstr(s_boson, 20),
    }


def local_check(beta_val: float = 2.0):
    primes = list(sp.primerange(2, 100))
    print("=== Single-mode microscopic accounting (one free example) ===")
    for p in [2, 3, 5]:
        print(f"prime p={p}")
        for state in local_two_level_spectrum(beta_val, p):
            print(
                "  ",
                state["state"],
                "E=",
                f"{state['energy']:.10g}",
                "grade=",
                state["supergrade"],
                "weight=",
                f"{state['weight']:.10g}",
            )
        print(f"  local factor Z_super(p)={super_local(beta_val, p):.12g}")
        print(
            f"  local mode identity: boson*super={super_local(beta_val, p) * boson_local(beta_val, p):.12g}"
        )
        print()

    Zs = super_partition(beta_val, primes)
    Zb = boson_partition(beta_val, primes)
    print("=== Finite cutoff dictionary (β=2.0, primes<100)")
    print("Z_super*Z_boson:", Zs * Zb)
    print("total CPT partition (Z_total):", cpt_total_partition(beta_val, primes))
    print("F_super + F_boson:", super_free_energy(beta_val, primes) + boson_free_energy(beta_val, primes))
    print("U_super + U_boson:", super_internal_energy(beta_val, primes) + boson_internal_energy(beta_val, primes))
    print("S_super + S_boson:", super_entropy(beta_val, primes) + boson_entropy(beta_val, primes))
    print("CPT totals:", cpt_total_free_energy(beta_val, primes), cpt_total_internal_energy(beta_val, primes), cpt_total_entropy(beta_val, primes))

    # finite Möbius/parity expansion check
    finite_primes = [2, 3, 5, 7, 11, 13]
    left = sym_super_partition(beta, finite_primes)
    right = sym_finite_mobius_expansion(beta, finite_primes)
    print("finite Möbius identity on first 6 primes:")
    print(" difference ∏(1-p^{-β}) - Σ ... =", sp.simplify(left - right))

    # CPT spectral action on local axis point s = β + i t
    b, t = sp.symbols("b t", real=True)
    print("CPT spectral map on axis:", sp.simplify(cpt_spectral_map(b, t)))
    cpt2 = sp.simplify(1 - sp.conjugate(1 - sp.conjugate((b + sp.I * t))))
    print("CPT²(s) =", cpt2)

    # parity diagnostics
    print("\n=== Möbius parity sign checks (sample) ===")
    for n in range(1, 17):
        print(f"n={n:2d}  Ω={omega_with_multiplicity(n)}  μ={parity_weight(n):2d}")

    # asymptotics in β
    print("\n=== Finite cutoff asymptotic probes ===")
    for b in [5.0, 10.0, 20.0, 40.0]:
        zs = super_partition(b, primes)
        print(f"β={b:.1f}: Z_super={zs:.12g}, F_super={super_free_energy(b, primes):.12g}")

    for b in [1.01, 1.05, 1.1, 1.2, 1.5]:
        zs = super_partition(b, primes)
        print(
            f"β={b:.2f}: Z_super={zs:.12g}, F_super={super_free_energy(b, primes):.12g}, "
            f"U_super={super_internal_energy(b, primes):.12g}"
        )

    print("\n=== Global symbolic reference via ζ(β)=Z_boson ===")
    for b in [2.0, 3.0, 4.0]:
        g = sym_global_zeta_probe(b)
        print(f"β={b:.1f}: Z_super=1/ζ={g['z_super']}")
        print(f"  F_super={g['F_super']}, U_super={g['U_super']}, S_super={g['S_super']}")
        print(f"  partner signs: F_boson={g['F_boson']}, U_boson={g['U_boson']}, S_boson={g['S_boson']}")
    for eps in [1e-3, 5e-3, 1e-2]:
        b = 1.0 + eps
        g = sym_global_zeta_probe(b)
        print(
            f"β→1+ ({b:.6f}): Z_super=1/ζ≈{g['z_super']}, "
            f"F_super≈{g['F_super']}, U_super≈{g['U_super']}, S_super≈{g['S_super']}"
        )

    print("\n=== Symbolic one-prime witness ===")
    sym_local_partition_witness()


if __name__ == "__main__":
    local_check(2.0)

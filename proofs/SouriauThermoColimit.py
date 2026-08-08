import sympy as sp
from typing import Callable

# ── Souriau/Pauli thermodynamic colimit witness ──
# Mirrors proofs/SouriauThermoColimit.lean: finite stages, stage-embedding,
# finite factors, boundary cocone profile, and parabolic lightcone criterion.

# Finite local factors

def ordinary_local(x):
    """Ordinary fermion local factor: 1 + x."""
    return 1 + x


def graded_local(x):
    """Graded/parity local factor: 1 - x.
    This is the finite Möbius/Witten local term.
    """
    return 1 - x


def boson_local(x):
    """Bosonic reciprocal local factor: (1 - x)⁻¹."""
    return (1 - x) ** (-1)


def finite_trace(xs, local):
    """Finite product over stage list with given local rule."""
    p = sp.Integer(1)
    for a in xs:
        p *= local(a)
    return sp.simplify(p)


def finiteOrdinaryTrace(xs):
    return finite_trace(xs, ordinary_local)


def finiteGradedSupertrace(xs):
    return finite_trace(xs, graded_local)


def finiteBosonicDeterminant(xs):
    return finite_trace(xs, boson_local)

# State labels matching the cubic OP branch `q^3 = q`.
class OPState:
    elliptic = "elliptic"      # q = 1   -> ordinary sector: 1 + x
    hyperbolic = "hyperbolic"  # q = -1  -> bosonic reciprocal sector: (1 - x)⁻¹
    parabolic = "parabolic"    # q = 0   -> graded/parity sector: 1 - x


def state_partition_local(state, x):
    """Local thermodynamic sector factor from OP-state."""
    if state == OPState.elliptic:
        return ordinary_local(x)
    if state == OPState.hyperbolic:
        return boson_local(x)
    if state == OPState.parabolic:
        return graded_local(x)
    raise ValueError(f"unknown OP state: {state}")


def state_partition(profile_x, profile_state):
    """Finite product partition with an OP-state profile."""
    if len(profile_x) != len(profile_state):
        raise ValueError("mismatch profile lengths")
    p = sp.Integer(1)
    for x, s in zip(profile_x, profile_state):
        p *= state_partition_local(s, x)
    return sp.simplify(p)


def cubic_roots(q):
    """Symbolic/simplified check: possible roots of q^3 = q in ℝ."""
    eq = sp.expand(q**3 - q)
    return [sp.solve(eq, q)]


# Stagewise finite cancellation identity

def finite_boson_cancels_graded(xs):
    """Formal cancellation law: bosonic determinant times graded product simplifies."""
    return sp.simplify(finiteBosonicDeterminant(xs) * finiteGradedSupertrace(xs))


# One-mode / two-mode checks used as symbolic sanity tests
x = sp.symbols("x")
y, z = sp.symbols("y z")
assert sp.simplify(finiteGradedSupertrace([x]) - graded_local(x)) == 0
assert (
    sp.expand(finiteGradedSupertrace([x, y, z]))
    == sp.expand((1 - x) * (1 - y) * (1 - z))
)

# State-profile partition sanity checks
assert state_partition([x], [OPState.elliptic]) == ordinary_local(x)
assert state_partition([x], [OPState.parabolic]) == graded_local(x)
assert sp.simplify(state_partition([x], [OPState.hyperbolic]) - boson_local(x)) == 0

# Mixed profile with one of each branch
assert sp.simplify(state_partition([x, y, z], [OPState.elliptic, OPState.parabolic, OPState.hyperbolic])
              - (1 + x) * (1 - y) * ((1 - z) ** -1)) == 0

# Symbolic cancellation law
assert sp.simplify(finiteBosonicDeterminant([x, y, z]) * finiteGradedSupertrace([x, y, z])) == 1

# Cubic branch identity q^3 = q has roots q∈{-1,0,1}
q = sp.symbols("q", real=True)
assert sp.factor(q**3 - q) == q * (q - 1) * (q + 1)


# ── Inductive/colimit-style stage construction ──


def souriau_embed(modes: Callable[[int], sp.Expr], n: int, v):
    """Append new mode `modes n` to finite stage vector."""
    return v + [modes(n)]


def finite_to_boundary(modes: Callable[[int], sp.Expr], n: int, v):
    """Boundary profile: first n entries are stage values; tail is source profile."""

    def profile(k: int):
        if k < n:
            return v[k]
        return modes(k)

    return profile


def stage_from_prefix(prefix):
    return list(prefix)


# Symbolic source mode profile and first-stage embedding chain (no concrete numerics)
modes = sp.Function("m")

v0 = stage_from_prefix([])
v1 = souriau_embed(modes, 0, v0)  # [m(0)]
v2 = souriau_embed(modes, 1, v1)  # [m(0), m(1)]
v3 = souriau_embed(modes, 2, v2)  # [m(0), m(1), m(2)]

# Boundary profile from stage n=2:
boundary_n2 = finite_to_boundary(modes, 2, v2)

assert boundary_n2(0) == modes(0)
assert boundary_n2(1) == modes(1)
assert boundary_n2(5) == modes(5)

# Show symbolic chain laws
assert v3 == [modes(0), modes(1), modes(2)]


# Singularity dictionary at finite stage

def souriau_denominator_zero(v):
    """Formal zero-denominator predicate at finite stage: ∃ local mode = 1."""
    if not v:
        return sp.false
    return sp.Or(*[sp.Eq(a, 1) for a in v])


def souriau_graded_index_singularity(v):
    """Graded index singularity predicate: finite graded product vanishes."""
    return sp.Eq(finiteGradedSupertrace(v), 0)


def moebius_denom_correspondence(v):
    """Formal implication used in the finite model: local singularity -> graded index singularity."""
    return sp.Implies(souriau_denominator_zero(v), souriau_graded_index_singularity(v))


def graded_index_zero_iff_denom_zero(v):
    """Formal one-way equivalence schema at finite stage.

    In generic symbolic settings we keep this as a conservative implication:
    denominator singularity gives graded singularity. Converse can be added
    with nondegeneracy hypotheses (mirroring Lean hypotheses).
    """
    return (souriau_denominator_zero(v), souriau_graded_index_singularity(v),
            moebius_denom_correspondence(v))


# Symbolic sample stage laws

a0, a1, a2 = sp.symbols("a0 a1 a2")
sample_stage = [a0, a1, a2]
assert finite_boson_cancels_graded(sample_stage) == 1
assert souriau_denominator_zero(sample_stage) == sp.Or(sp.Eq(a0, 1), sp.Eq(a1, 1), sp.Eq(a2, 1))
assert sp.simplify((1 - a0) * (1 - a1) * (1 - a2) - finiteGradedSupertrace(sample_stage)) == 0

# Degenerate singular sample
singular_stage = [a0, 1, a2]
assert souriau_denominator_zero(singular_stage) == sp.true
assert sp.simplify(finiteGradedSupertrace(singular_stage)) == 0


# ── parabolic/split lightcone degrees of freedom ──


class SplitParavector:
    def __init__(self, scalar, bivector):
        self.scalar = sp.sympify(scalar)
        self.bivector = sp.sympify(bivector)

    def det(self):
        return sp.expand(self.scalar ** 2 - self.bivector ** 2)

    def parabolic(self):
        return sp.Eq(self.det(), 0)


def paravectorTemperature(sigma, gamma):
    return SplitParavector(sigma, gamma)


def paravectorTemperature_det(sigma, gamma):
    return paravectorTemperature(sigma, gamma).det()


def paravectorLightcone_iff(sigma, gamma):
    """Split lightcone criterion in algebraic form: Δ=σ²-γ²=0."""
    return sp.Eq(paravectorTemperature_det(sigma, gamma), 0)


# Quick check of the lightcone marker
σ, γ = sp.symbols("σ γ", real=True)
assert paravectorTemperature_det(σ, γ) == σ ** 2 - γ ** 2


# print witness summary
print("SouriauThermoColimit.py: finite Pauli-Souriau thermodynamic colimit witness loaded")
print("  ordinary local factor:     f_+ (x) =", ordinary_local(x))
print("  graded local factor:      f_− (x) =", graded_local(x))
print("  boson local factor:       f_B (x) =", boson_local(x))
print("  one-stage graded product:", finiteGradedSupertrace([x]), "= 1-x")
print("  finite graded/bosonic cancellation (formal):")
print("    ∏_i (1-a_i)·∏_i (1-a_i)⁻¹ =", finite_boson_cancels_graded(sample_stage))
print("  denominator-singularity predicate on sample: ", souriau_denominator_zero(sample_stage))
print("  graded singularity predicate on sample:      ", souriau_graded_index_singularity(sample_stage))
print("  Möbius implication on sample:               ", moebius_denom_correspondence(sample_stage))
print("  singular sample graded index =", finiteGradedSupertrace(singular_stage))
print("  boundary profile v2 @0/1/5 =", boundary_n2(0), boundary_n2(1), boundary_n2(5))
print("  paravector det Δ(σ,γ)=", paravectorTemperature_det(σ, γ))
print("  parabolic predicate =", paravectorLightcone_iff(σ, γ))
print("  formal pole at local singular x=1 -> graded index =", finiteGradedSupertrace([1]))

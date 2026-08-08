import sympy as sp

# Layer-11 spectral-thermodynamic dictionary for zeta language.

sigma, t = sp.symbols("sigma t", real=True)
s = sigma + sp.I * t

# Basic complex-temperature split

def complex_temperature(σ, τ):
    return (σ) + sp.I * (τ)

assert sp.re(complex_temperature(sigma, t)) == sigma
assert sp.im(complex_temperature(sigma, t)) == t

# Hagedorn/pole coordinate
hagedorn_temperature = sp.Integer(1)

# finite core phase/weight/truncation
def arithmetic_phase(time, n):
    return sp.exp(-sp.I * time * sp.log(n))


def damping_weight(damping, n):
    return n ** (-damping)


def finite_complex_trace(damping, time, cutoff):
    return sum(
        damping_weight(damping, n) * arithmetic_phase(time, n)
        for n in range(1, cutoff + 1)
    )

for n in range(1, 12):
    assert sp.simplify(arithmetic_phase(0, n) - 1) == 0

for cutoff in range(1, 8):
    assert sp.simplify(
        finite_complex_trace(sigma, 0, cutoff)
        - sum(damping_weight(sigma, n) for n in range(1, cutoff + 1))
    ) == 0

# Bosonic / ordinary fermionic / graded fermionic primon partitions (formal dictionary)

def bosonic_primon_partition(Z, z):
    return Z(z)


def ordinary_fermionic_primon_partition(Z, z):
    return bosonic_primon_partition(Z, z) / bosonic_primon_partition(Z, 2 * z)


def graded_fermionic_primon_partition(Z, z):
    return sp.Integer(1) / bosonic_primon_partition(Z, z)

def moebius_dirichlet_series(Z, z):
    return graded_fermionic_primon_partition(Z, z)


def graded_supertrace_singularity(Z, z):
    return sp.simplify(Z(z)) == 0


def graded_index_pole_condition(Z, z):
    return sp.simplify(moebius_dirichlet_series(Z, z)) == sp.zoo

# local algebraic identity
Z = sp.Function("Z")
gamma = sp.symbols("gamma", real=True)
hilbert_polya_zero_shape = sp.Rational(1, 2) + sp.I * gamma
assert sp.re(hilbert_polya_zero_shape) == sp.Rational(1, 2)
assert sp.im(hilbert_polya_zero_shape) == gamma

# Hagedorn model and pole relation
pole_model = sp.Integer(1) / (s - hagedorn_temperature)
assert sp.simplify(pole_model * (s - hagedorn_temperature) - 1) == 0

# Critical-line characterization under the complex-temperature chart
assert sp.simplify(sp.re(complex_temperature(sp.Rational(1, 2), t)) - sp.Rational(1, 2)) == 0

# Graded index at a formal mock zero
mock_zero = sp.symbols("s0")
assert sp.simplify(graded_fermionic_primon_partition(lambda x: (x - mock_zero), mock_zero)) == sp.zoo
assert graded_supertrace_singularity(lambda x: (x - mock_zero), mock_zero) == True
# For the toy denominator Z=0 at mock_zero, the Möbius-index is singular
assert str(moebius_dirichlet_series(lambda x: (x - mock_zero), mock_zero)) == 'zoo'

# Formal zero-locus marker (symbolic)
Zmock = sp.Function("Z")(mock_zero)
print("RiemannHypothesis.py: theorem-honest complex-temperature dictionary verified")
print("  complexTemperature(σ,t) =", complex_temperature(sigma, t))
print("  Hagedorn pole coordinate at s =", hagedorn_temperature)
print("  bosonic singular template: zeta ↦ 1/(s-1)")
print("  critical-line template: σ = 1/2 (from Re(s))")
print("  formal ordinary fermionic factor relation: Z_F = Z / Z(2s)")
print("  formal graded fermionic factor: Z_gr = 1/Z")
print("  formal mock zero condition: if Z(mock_zero)=0, then 1/Z(mock_zero) is singular")
print("  moebius model at mock zero:", moebius_dirichlet_series(lambda x: (x - mock_zero), mock_zero))

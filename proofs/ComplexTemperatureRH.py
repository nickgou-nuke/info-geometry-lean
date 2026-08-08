import sympy as sp

# ── Complex-temperature dictionary for the partition-function model of zeta ──

beta, t = sp.symbols("beta t", real=True)

n = sp.symbols("n", positive=True, integer=True)
s = beta + sp.I * t

# 1) complex temperature and coordinates

def damping_strength(x):
    """Real part of s = beta + i t."""
    return sp.re(x)


def oscillatory_phase(x):
    """Imaginary part / phase of s = beta + i t."""
    return sp.im(x)

assert damping_strength(s) == beta
assert oscillatory_phase(s) == t

# 2) toy partition functions for complex temperatures

def bosonic_partition(s_val):
    """Bosonic primon partition `Z_B(s)=ζ(s)` in symbolic form."""
    return sp.zeta(s_val)


def ordinary_fermionic_partition(s_val):
    """Ordinary fermionic primon partition: `∏(1+p^{-s}) = ζ(s)/ζ(2s)`."""
    return sp.zeta(s_val) / sp.zeta(2 * s_val)


def graded_fermionic_index(s_val):
    """Graded fermionic index: `Tr((-1)^F e^{-sH}) = 1/ζ(s)`."""
    return sp.Integer(1) / sp.zeta(s_val)


# 3) finite complex trace: sum_{n=1}^N n^{-s}

def arithmetic_phase(time, nval):
    return sp.exp(-sp.I * time * sp.log(nval))


def finite_complex_trace(beta_val, time, cutoff):
    """Truncated analytic-series partition term: Σ_{n=1}^N n^{-beta} * e^{-i t log n}."""
    return sp.summation(n ** (-beta_val) * arithmetic_phase(time, n), (n, 1, cutoff))


def finite_complex_trace_parts(beta_val, time, cutoff):
    """Same split into damping * oscillatory part."""
    return sp.summation((n ** (-beta_val)) * sp.exp(-sp.I * time * sp.log(n)), (n, 1, cutoff))


def finite_real_thermal_trace(beta_val, cutoff):
    return sp.summation((n ** (-beta_val)), (n, 1, cutoff))

# checks
for N in range(1, 8):
    assert sp.simplify(finite_complex_trace(beta, 0, N) - finite_real_thermal_trace(beta, N)) == 0
    assert sp.simplify(finite_complex_trace_parts(beta, 0, N) - finite_real_thermal_trace(beta, N)) == 0

# 4) cancellation/interference vocabulary

def cancellation_condition(beta_val, time, cutoff):
    return sp.Eq(finite_complex_trace(beta_val, time, cutoff), 0)

# algebraic core identities (formal)
assert sp.simplify(ordinary_fermionic_partition(s) * sp.zeta(2 * s) - sp.zeta(s)) == 0

# 5) critical-line zero template and index pole/zero language

gamma = sp.symbols("gamma", real=True)
critical_zero_shape = sp.Rational(1, 2) + sp.I * gamma
assert sp.re(critical_zero_shape) == sp.Rational(1, 2)
assert sp.im(critical_zero_shape) == gamma

# Evaluate symbolic local behavior of reciprocal near a zero: if ζ(s0)=0 then 1/ζ(s0) is singular.
# (Here represented symbolically: `1/0` is the usual algebraic marker of a pole.)

# 6) finite Euler-product/log-expansion illustration

def euler_log_fundamentals(s_val, primes):
    """Finite Euler product logarithm in terms of prime powers."""
    finite_euler = sp.Mul(*((1 - p ** (-s_val)) ** (-1) for p in primes))
    return sp.expand_log(finite_euler)

# prime/prime-power mode sample
s_test = sp.Symbol("s", complex=True)
prime_terms = euler_log_fundamentals(s_test, [2, 3, 5])

# A finite approximation of the Möbius/graded expansion `1/ζ(s) = Σ μ(n)/n^s`.
# (Only a structural pattern in this file, not a convergent full identity.)
def mobius_expansion_cutoff(s_val, cutoff):
    k = sp.symbols("k", integer=True, positive=True)
    return sp.summation(sp.mobius(k) / (k ** s_val), (k, 1, cutoff))

finite_mu_8 = sp.simplify(mobius_expansion_cutoff(s_test, 8))

# 7) symbolic summary + optional numeric probe

def numeric_probe(first_gamma, eps=sp.Rational(1, 10**6)):
    """Optional numeric probe (not part of theorem statements)."""
    nz = sp.N(sp.Rational(1, 2) + sp.I * first_gamma, 30)
    zeta_nz = sp.N(sp.zeta(nz), 25)
    nz_up = sp.N(sp.Rational(1, 2) + sp.I * (first_gamma + eps), 25)
    zeta_up = abs(sp.N(sp.zeta(nz_up), 30))
    inv_up = abs(sp.N(sp.Integer(1) / sp.zeta(nz_up), 30))
    return zeta_nz, zeta_up, inv_up

# symbolic pole marker at a formal zero of Z(s)
z0 = sp.symbols("s0")
formal_boson = bosonic_partition(z0)
formal_graded = graded_fermionic_index(z0)
formal_singularity = sp.Eq(formal_boson, 0)
formal_divergence = graded_fermionic_index(z0)

print("ComplexTemperatureRH.py: partition-function frame checks passed")
print("  s                    =", s)
print("  Re(s)                =", damping_strength(s))
print("  Im(s)                =", oscillatory_phase(s))
print("  bosonic Z_B(s)       =", bosonic_partition(s))
print("  ordinary fermion Z_F(s)=", ordinary_fermionic_partition(s))
print("  graded fermion 1/Z_B(s)=", graded_fermionic_index(s))
N = sp.symbols("N", integer=True, positive=True)
print("  finite trace at t=0, N =", finite_complex_trace(beta, 0, N))
print("  critical-zero template =", critical_zero_shape)
print("  finite Euler log sample =", sp.simplify(prime_terms))
print("  finite Möbius sample    =", finite_mu_8)
print("  formal zero locus      =", formal_singularity)
print("  formal graded pole marker=", formal_divergence)
print("  key split:")
print("   - pole at s=1 is bosonic Hagedorn growth in Z_B")
print("   - zeros of bosonic denominator correspond to poles of graded index (formal)")
print("   - ordinary fermionic factor remains formal quotient Z(s)/Z(2s)")

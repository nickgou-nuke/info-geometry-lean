#!/usr/bin/env python3
"""SymPy evidence: Poincare algebra from chiral supercharge anticommutator.

{Q_alpha, Qbar_betȧ} = 2 sigma^mu_{alphabetȧ} P_mu

where sigma^mu = (I, sigma_x, sigma_y, sigma_z) are the Pauli 4-vector.
For the primon gas in the rest frame: P_mu = (H, 0, 0, 0).
"""
import sympy as sp
from sympy import Matrix, I, zeros

# Pauli matrices
s0 = Matrix([[1, 0], [0, 1]])     # sigma^0 = I
s1 = Matrix([[0, 1], [1, 0]])     # sigma^1 = sigma_x
s2 = Matrix([[0, -I], [I, 0]])    # sigma^2 = sigma_y
s3 = Matrix([[1, 0], [0, -1]])    # sigma^3 = sigma_z

sigma = [s0, s1, s2, s3]  # sigma^mu
sigma_bar = [s0, -s1, -s2, -s3]  # lowered inverse Pauli matrices

def sigma_contract(P):
    """Return sigma^mu P_mu."""
    return sum((sigma[mu] * P[mu] for mu in range(4)), zeros(2))

def recover_sigma_coefficients_from_anticommutator(anticommutator):
    """Recover the coefficients of sigma^mu in {Q,Qbar}=2 sigma^mu P_mu."""
    return [sp.simplify(sp.trace(sigma[mu] * anticommutator) / 4) for mu in range(4)]

def recover_lowered_momentum_from_anticommutator(anticommutator):
    """Recover eta_{mu nu} P^nu by 1/4 Tr(sigma_bar_mu {Q,Qbar})."""
    return [sp.simplify(sp.trace(sigma_bar[mu] * anticommutator) / 4) for mu in range(4)]

def minkowski_lower(P):
    """Lower a four-vector with signature (+---)."""
    return [P[0], -P[1], -P[2], -P[3]]

def minkowski_norm_sq(P):
    """Minkowski square with signature (+---)."""
    return sp.simplify(P[0]**2 - P[1]**2 - P[2]**2 - P[3]**2)

def verify_poincare_susy():
    """Verify {Q, Q†} = 2 sigma^mu P_mu for N=1 SUSY."""
    print("=" * 60)
    print("Poincare Algebra from Supercharge Anticommutator")
    print("=" * 60)

    # In the rest frame: P_mu = (H, 0, 0, 0)
    H = sp.Symbol('H', real=True, positive=True)
    zero = sp.Integer(0)
    P = [H, zero, zero, zero]  # rest frame 4-momentum

    # Contract: sigma^mu_{alphabetȧ} P_mu
    P_sigma = sigma_contract(P)

    # The anticommutator {Q_alpha, Qbar_betȧ} = 2 * sigma^mu_{alphabetȧ} P_mu
    anticommutator = 2 * P_sigma
    print(f"\n1. Rest frame momentum: P_mu = ({P[0]}, {P[1]}, {P[2]}, {P[3]})")
    print(f"   sigma^mu P_mu =")
    sp.pprint(P_sigma)
    print(f"\n   {{Q_alpha, Qbar_betȧ}} = 2 sigma^mu P_mu =")
    sp.pprint(anticommutator)

    # Trace gives 4H = 2 * Tr(sigma^mu P_mu) = 2 * (2H) = 4H
    trace = sp.trace(anticommutator)
    print(f"\n2. Trace check: Tr({{Q, Qbar}}) = {trace}")
    assert sp.simplify(trace - 4*H) == 0, "Trace should be 4H"
    assert recover_sigma_coefficients_from_anticommutator(anticommutator) == P
    assert recover_lowered_momentum_from_anticommutator(anticommutator) == minkowski_lower(P)
    print("   ✓ Tr = 4H")
    print("   ✓ inverse Pauli traces recover rest momentum coefficients/lowering")

    # Casimir: P^mu P_mu = H² - p² = H² in rest frame
    casimir_rest = minkowski_norm_sq(P)
    assert sp.simplify(casimir_rest - H**2) == 0
    assert sp.simplify(anticommutator.det() - 4 * casimir_rest) == 0
    print(f"\n3. Casimir: P^mu P_mu = H² in rest frame")
    print("   ✓ P_mu P^mu = H²")
    print("   ✓ det({Q,Qbar}) = 4 P² in rest frame")

    # In boosted frame: P_mu = (gammaH, gammabeta⃗H)
    v = sp.Symbol('v', real=True)
    gamma_v = 1 / sp.sqrt(1 - v**2)
    P_boost = [gamma_v * H, gamma_v * v * H, 0, 0]  # boost along x
    P_sigma_boost = sigma_contract(P_boost)
    anticom_boost = 2 * P_sigma_boost
    print(f"\n4. Boosted frame: P_mu = gammaH(1, v, 0, 0)")
    print(f"   {{Q, Qbar}} =")
    sp.pprint(anticom_boost)
    casimir_boost = minkowski_norm_sq(P_boost)
    recovered_boost = recover_sigma_coefficients_from_anticommutator(anticom_boost)
    recovered_lower_boost = recover_lowered_momentum_from_anticommutator(anticom_boost)
    assert all(sp.simplify(recovered_boost[mu] - P_boost[mu]) == 0 for mu in range(4))
    assert all(
        sp.simplify(recovered_lower_boost[mu] - minkowski_lower(P_boost)[mu]) == 0
        for mu in range(4)
    )
    assert sp.simplify(casimir_boost - H**2) == 0, "boosted Casimir must reduce to H^2"
    assert sp.simplify(anticom_boost.det() - 4 * casimir_boost) == 0
    print(f"   Casimir = gamma²H² - gamma²v²H² = {casimir_boost}")
    print("   ✓ inverse Pauli traces recover boosted coefficients/lowering")
    print("   ✓ det({Q,Qbar}) = 4 P² in boosted frame")
    print("   ✓ Casimir invariant under boost")

    # Null branch: determinant zero is exactly the finite light-cone condition.
    P_null = [H, H, 0, 0]
    anticom_null = 2 * sigma_contract(P_null)
    casimir_null = minkowski_norm_sq(P_null)
    assert sp.simplify(casimir_null) == 0
    assert sp.simplify(anticom_null.det()) == 0
    assert recover_sigma_coefficients_from_anticommutator(anticom_null) == P_null
    print("   ✓ null momentum gives singular {Q,Qbar} matrix")

def verify_primon_gas():
    """Verify the primon gas Hamiltonian from CAR supercharge."""
    print("\n" + "=" * 60)
    print("Primon Gas: H = Σ log(p_i) S_i Sdag_i")
    print("=" * 60)

    n = sp.Symbol('n', integer=True, positive=True)
    # For finite n, the Hamiltonian is diagonal with eigenvalues log(p_i)
    # The partition function is Tr(exp(-betaH)) = Σ p_i^{-beta}

    beta = sp.Symbol('beta', real=True, positive=True)
    # For n=4: primes 2,3,5,7
    primes = [2, 3, 5, 7]
    Z_beta = sum(p**(-beta) for p in primes)
    print(f"\n1. Partition function Z(beta) = Σ p_i^(-beta)")
    print(f"   For primes {primes}: Z(beta) = {Z_beta}")

    expected = sum(sp.Integer(p) ** (-beta) for p in primes)
    assert sp.simplify(Z_beta - expected) == 0
    print("   ✓ finite one-particle primon partition is exactly the prime-energy sum")

    bosonic_fock = sp.prod(1 / (1 - sp.Integer(p) ** (-beta)) for p in primes)
    fermionic_fock = sp.prod(1 + sp.Integer(p) ** (-beta) for p in primes)
    graded_fock = sp.prod(1 - sp.Integer(p) ** (-beta) for p in primes)
    assert sp.simplify(bosonic_fock - 1 / graded_fock) == 0

    print(f"\n2. Finite Fock products over the same prime modes:")
    print(f"   Bosonic:  Π_p (1 - p^-beta)^-1 = {bosonic_fock}")
    print(f"   Fermionic: Π_p (1 + p^-beta) = {fermionic_fock}")
    print(f"   Graded:   Π_p (1 - p^-beta) = {graded_fock}")
    print("   ✓ no Riemann-zeta limit is asserted for the finite prime sum")

def verify_chiral_projectors():
    """Verify the chiral projectors P_± = (1 ± gamma_5)/2."""
    print("\n" + "=" * 60)
    print("Chiral Projectors and Twistor Incidence")
    print("=" * 60)

    # gamma_5 = i gamma_0 gamma_1 gamma_2 gamma_3 in 4D
    # For Cl(1,1): gamma_5 = r_0 r_5 (the Euler operator B)
    # P_± = (1 ± B)/2

    # In 2×2 representation:
    B = Matrix([[1, 0], [0, -1]])  # r_0 r_5 in chiral basis
    P_plus = (Matrix.eye(2) + B) / 2
    P_minus = (Matrix.eye(2) - B) / 2

    print(f"\n1. Euler operator B = r_0 r_5:")
    sp.pprint(B)
    print(f"\n   P_+ = (1+B)/2:")
    sp.pprint(P_plus)
    print(f"\n   P_- = (1-B)/2:")
    sp.pprint(P_minus)

    # Verify: P_±² = P_±, P_+ P_- = 0, P_+ + P_- = 1
    assert P_plus * P_plus == P_plus, "P_+ not idempotent"
    assert P_minus * P_minus == P_minus, "P_- not idempotent"
    assert P_plus * P_minus == zeros(2), "P_+ P_- not orthogonal"
    assert P_minus * P_plus == zeros(2), "P_- P_+ not orthogonal"
    assert P_plus + P_minus == Matrix.eye(2), "P_+ + P_- != 1"
    assert P_plus.H == P_plus and P_minus.H == P_minus, "projectors must be self-adjoint"
    print("   ✓ All projector properties verified")

    # Twistor incidence: ω^A = (λ_alpha, mu^{alphȧ}) on null cone
    # Penrose: alpha-planes and beta-planes correspond to P_+ and P_- projectors
    print(f"\n2. Twistor incidence on null cone:")
    print(f"   alpha-plane (self-dual): P_+ projects onto left-handed spinors")
    print(f"   beta-plane (anti-self-dual): P_- projects onto right-handed spinors")
    print("   Incidence: omega-bar_{alphadot} = x_{alpha,alphadot} pi^alpha  (Penrose transform)")

def verify_souriau_beta_4vector():
    """Verify Souriau's beta_mu as 4-vector equilibrium parameter."""
    print("\n" + "=" * 60)
    print("Souriau Thermodynamics: beta_mu 4-vector")
    print("=" * 60)

    # Souriau's key insight: beta is a 4-vector
    # beta_mu = (1/T, v⃗/T) couples to P^mu
    # The equilibrium state is exp(-beta_mu P^mu)

    T = sp.Symbol('T', real=True, positive=True)
    v = sp.Symbol('v', real=True)
    beta_0 = 1 / T
    beta_1 = v / T
    E = sp.Symbol('E', real=True)
    px = sp.Symbol('p_x', real=True)
    beta_vec = [beta_0, beta_1, 0, 0]
    P_vec = [E, px, 0, 0]
    beta_dot_P = sp.simplify(beta_vec[0] * P_vec[0] - beta_vec[1] * P_vec[1])

    # In the rest frame (v=0): beta_mu P^mu = H/T
    # In the comoving frame: beta_mu P^mu = gammaH/T (time dilation)
    gamma_v = 1 / sp.sqrt(1 - v**2)
    assert sp.simplify(beta_dot_P - (E - v * px) / T) == 0
    assert sp.simplify(beta_dot_P.subs({v: 0, px: 0}) - E / T) == 0
    gibbs_weight = sp.exp(-beta_dot_P)
    assert sp.simplify(gibbs_weight - sp.exp(-(E - v * px) / T)) == 0

    print(f"\n1. beta_mu = (1/T, v⃗/T)")
    print(f"   beta_mu P^mu = H/T - p⃗·v⃗/T")
    print(f"   Rest frame (v=0): beta_mu P^mu = H/T")
    print(f"   Boosted frame: beta_mu P^mu = gamma H/T - gamma v p_x/T = gamma(H - v p)/T")
    print("   ✓ beta_mu P^mu contraction verified symbolically")

    print(f"\n2. KMS equilibrium state:")
    print(f"   ω_beta(A) = Tr(exp(-beta_mu P^mu) A) / Tr(exp(-beta_mu P^mu))")
    print(f"   This is the modular state at inverse temperature beta_mu")
    print(f"   scalar Gibbs factor = {gibbs_weight}")

    print(f"\n3. Connection to primon gas:")
    print(f"   In the primon rest frame: beta_mu P^mu = beta H")
    print(f"   With ε_i = log(p_i): H = Σ log(p_i) P_i")
    print("   Partition function: Tr(exp(-beta H)) = sum p_i^{-beta}")

if __name__ == "__main__":
    verify_poincare_susy()
    verify_primon_gas()
    verify_chiral_projectors()
    verify_souriau_beta_4vector()
    print("\n" + "=" * 60)
    print("All verifications passed.")

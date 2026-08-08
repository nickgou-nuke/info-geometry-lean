import sympy as sp

# ── Canonical Souriau thermodynamics for Pauli algebra (toy model) ──

# Pauli dual space: R^3 of spin-spatial thermodynamic charges

def pauli_axis(a, b, c):
    """Canonical 3-vector embedding for axis coordinates."""
    return sp.Matrix([a, b, c])


def pauli_pairing(beta, J):
    """Canonical dual pairing ⟨β, J⟩ = β·J on 3-vectors."""
    return sp.expand(sum(b * j for b, j in zip(beta, J)))


def pauli_boltzmann_weight(beta, J):
    """Local Gibbs/Boltzmann factor exp(-⟨β, J⟩) for 3-vectors."""
    return sp.exp(-pauli_pairing(beta, J))


def pauli_local_partition(beta, J):
    """One-mode Pauli grand-canonical local factor: 1 + exp(-⟨β, J⟩)."""
    return sp.simplify(1 + pauli_boltzmann_weight(beta, J))


# Canonical one-axis specialization (e.g. z-axis)
def pauli_axis_partition(beta_z, xi_z):
    return pauli_local_partition(pauli_axis(0, 0, beta_z), pauli_axis(0, 0, xi_z))

# Full 4-component paravector form (s0, s1, s2, s3)

def pauli_axis4(t, x, y, z):
    """Canonical 4-axis embedding `(t,x,y,z)`."""
    return sp.Matrix([t, x, y, z])


def pauli_paravector_pairing(beta, J):
    """Paravector pairing ⟨β, J⟩ = β0 J0 + β1 J1 + β2 J2 + β3 J3."""
    return sp.expand(sum(b * j for b, j in zip(beta, J)))


def pauli_paravector_boltzmann_weight(beta, J):
    """Paravector Gibbs/Boltzmann factor exp(-⟨β, J⟩)."""
    return sp.exp(-pauli_paravector_pairing(beta, J))


def pauli_paravector_local_partition(beta, J):
    """Paravector one-mode local factor: 1 + exp(-⟨β, J⟩)."""
    return sp.simplify(1 + pauli_paravector_boltzmann_weight(beta, J))


def pauli_from3(s0, beta):
    """Lift a 3-vector to paravector by adding scalar slot `s0` in position 0."""
    return sp.Matrix([s0, beta[0], beta[1], beta[2]])

def pauli_scale_weyl(lam, v):
    """Free Weyl scale action on 4-vector: v ↦ lam·v."""
    return sp.Matrix([lam * c for c in v])


# Pauli matrices

def pauli_matrices():
    I2 = sp.eye(2)
    I = sp.I
    sigma_x = sp.Matrix([[0, 1], [1, 0]])
    sigma_y = sp.Matrix([[0, -I], [I, 0]])
    sigma_z = sp.Matrix([[1, 0], [0, -1]])
    return I2, sigma_x, sigma_y, sigma_z


def pauli_hamiltonian(h0, hx, hy, hz):
    """Concrete Pauli-form Hamiltonian H = h0 I + hx σx + hy σy + hz σz."""
    I2, sx, sy, sz = pauli_matrices()
    return sp.expand(h0) * I2 + sp.expand(hx) * sx + sp.expand(hy) * sy + sp.expand(hz) * sz


def pauli_ham_det(h0, hx, hy, hz):
    H = pauli_hamiltonian(h0, hx, hy, hz)
    return sp.expand(sp.factor(H.det()))


def pauli_ham_trace(h0, hx, hy, hz):
    H = pauli_hamiltonian(h0, hx, hy, hz)
    return sp.expand(H.trace())


# ── Symbolic sanity checks ──

beta = sp.symbols("beta", real=True)
xi = sp.symbols("xi", real=True)
b1, b2, b3, j1, j2, j3 = sp.symbols("b1 b2 b3 j1 j2 j3", real=True)

# 3-vector checks
assert pauli_pairing(pauli_axis(b1, b2, b3), pauli_axis(j1, j2, j3)) == b1*j1 + b2*j2 + b3*j3
assert pauli_local_partition(pauli_axis(0, 0, beta), pauli_axis(0, 0, xi)) == 1 + sp.exp(-(beta*xi))

# 4-component (paravector) checks
assert pauli_paravector_pairing(pauli_axis4(1, 2, 3, 4), pauli_axis4(5, 6, 7, 8)) == 1*5 + 2*6 + 3*7 + 4*8
beta0 = sp.symbols("beta0", real=True)
assert sp.simplify(
    pauli_paravector_pairing(pauli_from3(beta0, pauli_axis(b1, b2, b3)), pauli_from3(1, pauli_axis(j1, j2, j3)))
    - (beta0 + b1*j1 + b2*j2 + b3*j3)
) == 0

# free scalar slots
J0 = sp.symbols("J0", real=True)
assert sp.simplify(
    pauli_paravector_pairing(
        pauli_from3(beta0, pauli_axis(b1, b2, b3)),
        pauli_from3(J0, pauli_axis(j1, j2, j3))
    )
    - (beta0 * J0 + b1*j1 + b2*j2 + b3*j3)
) == 0

assert sp.simplify(
    pauli_paravector_boltzmann_weight(pauli_from3(beta0, pauli_axis(b1, b2, b3)), pauli_from3(1, pauli_axis(j1, j2, j3)))
    - sp.exp(-beta0) * sp.exp(-(b1*j1 + b2*j2 + b3*j3))
) == 0

lam = sp.symbols("lam", nonzero=True, real=True)
assert sp.simplify(
    pauli_paravector_pairing(
        pauli_scale_weyl(lam, pauli_from3(beta0, pauli_axis(b1, b2, b3))),
        pauli_scale_weyl(1/lam, pauli_from3(J0, pauli_axis(j1, j2, j3)))
    )
    - pauli_paravector_pairing(pauli_from3(beta0, pauli_axis(b1, b2, b3)), pauli_from3(J0, pauli_axis(j1, j2, j3)))
) == 0

assert sp.simplify(
    pauli_paravector_boltzmann_weight(
        pauli_scale_weyl(lam, pauli_from3(beta0, pauli_axis(b1, b2, b3))),
        pauli_scale_weyl(1/lam, pauli_from3(J0, pauli_axis(j1, j2, j3)))
    )
    - pauli_paravector_boltzmann_weight(pauli_from3(beta0, pauli_axis(b1, b2, b3)), pauli_from3(J0, pauli_axis(j1, j2, j3)))
) == 0

h0, hx, hy, hz = sp.symbols("h0 hx hy hz", real=True)
assert pauli_ham_det(h0, hx, hy, hz) == h0**2 - (hx**2 + hy**2 + hz**2)
assert pauli_ham_trace(h0, hx, hy, hz) == 2*h0

# quick display
print("CanonicalSouriauPauliThermodynamics.py loaded")
print("pairing(β,J) :=", pauli_pairing(pauli_axis(1, 2, 3), pauli_axis(4, 5, 6)))
print("axis partition βz=2, ξz=3:", sp.simplify(pauli_axis_partition(2, 3)))
print("4-axis pairing (t,x,y,z):", pauli_paravector_pairing(pauli_axis4(1, 2, 3, 4), pauli_axis4(2, 3, 4, 5)))
print("paravector Gibbs factor (with J0=1):", pauli_paravector_boltzmann_weight(pauli_from3(2, pauli_axis(1, 2, 3)), pauli_from3(1, pauli_axis(4, 5, 6))))
print("H det =", pauli_ham_det(1, 2, 3, 4))
print("H trace =", pauli_ham_trace(1, 2, 3, 4))

# Bridge-note check: determinant sign sector is invariant under nonzero real rescaling.
def weyl_sector_det2(a, b, c, d):
    dlt = a * d - b * c
    if dlt > 0:
        return "+"
    if dlt < 0:
        return "-"
    return "0"

M = sp.Matrix([[1, 2], [3, 4]])
lam = sp.Integer(7)
M_scaled = lam * M
print("det(M)=", M.det(), " det(λM)=", M_scaled.det(), "same Weyl sector:", weyl_sector_det2(1, 2, 3, 4) == weyl_sector_det2(7, 14, 21, 28))

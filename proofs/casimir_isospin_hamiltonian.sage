var("m2 J T v Tz alpha beta gamma delta a b c k0 k1 spring t")

def mass_casimir(x):
    return -x

def spin_casimir(x):
    return x * (x + 1)

def isospin_casimir(x):
    return x * (x + 1)

def seniority_casimir(x):
    return x * (x + 1)

def stiffness(C):
    return -C

def imme(a0, b0, c0, tz):
    return a0 + b0 * tz + c0 * tz^2

def pair_hamiltonian(k0v, k1v):
    return k0v + k1v

def casimir_hamiltonian(alpha0, beta0, gamma0, delta0, m20, J0, T0, v0):
    return alpha0 * mass_casimir(m20) + beta0 * spin_casimir(J0) + gamma0 * isospin_casimir(T0) + delta0 * seniority_casimir(v0)

def generalized(alpha0, beta0, gamma0, delta0, a0, b0, c0, k0v, k1v, spring0, m20, J0, T0, v0, tz):
    return casimir_hamiltonian(alpha0, beta0, gamma0, delta0, m20, J0, T0, v0) + imme(a0, b0, c0, tz) + pair_hamiltonian(k0v, k1v) + spring0

H = lambda x: generalized(alpha, beta, gamma, delta, a, b, c, k0, k1, spring, m2, J, T, v, x)

assert isospin_casimir(1) == 2
assert isospin_casimir(QQ(1)/2) == QQ(3)/4
assert expand(stiffness(mass_casimir(m2)) - m2) == 0
assert expand(imme(a,b,c,t) - imme(a,b,c,-t) - 2*b*t) == 0
assert expand(imme(a,b,c,t) + imme(a,b,c,-t) - (2*a + 2*c*t^2)) == 0
assert expand(H(t) - H(-t) - 2*b*t) == 0
assert stiffness(mass_casimir(94)) == 94

print({
    "C_T_T1": 2,
    "C_T_half": QQ(3)/4,
    "mass_stiffness_94": 94,
    "mirror_difference": "2*b*t",
    "pair_channels": 2,
    "edges": 5,
})

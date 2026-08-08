import sympy as sp

Q = sp.Rational

def orbit(action, group_elements, x):
    return {action(g, x) for g in group_elements}

def invariant(action, group_elements, points, f):
    return all(f(action(g, x)) == f(x) for g in group_elements for x in points)

def entropy_from_casimirs(C1, C2, a, b, c, x):
    return sp.factor(a * C1(x) + b * C2(x) + c)

G = [-1, 1]
X = [Q(-1, 2), Q(1, 2)]
flip = lambda g, x: g * x
C_isospin = lambda x: x**2
C_spin = lambda x: Q(3, 4)

assert invariant(flip, G, X, C_isospin)
assert invariant(flip, G, X, C_spin)

a, b, c = sp.symbols("a b c")
S = lambda x: entropy_from_casimirs(C_isospin, C_spin, a, b, c, x)
assert invariant(flip, G, X, S)
assert orbit(flip, G, Q(1, 2)) == {Q(-1, 2), Q(1, 2)}
assert S(Q(-1, 2)) == S(Q(1, 2))

def isospin_casimir(I):
    return sp.factor(I * (I + 1))

assert isospin_casimir(Q(1, 2)) == Q(3, 4)
assert Q(-1, 2) + Q(1, 2) == 0

def poincare_mass_casimir(mass_sq):
    return -mass_sq

def dilation_spring_stiffness(C1):
    return -C1

assert dilation_spring_stiffness(poincare_mass_casimir(Q(67))) == 67

def ivgmr_coefficient(A, e, R, deltaE0):
    return Q(A - 1) * Q(e) ** 2 / (4 * Q(R) * Q(deltaE0))

def ivgmr_one_body_radial(ri, R):
    return Q(ri) ** 3 / Q(R) ** 2

def ivgmr_two_body_radial(ri, rj, R):
    return Q(ri) * Q(rj) ** 2 / Q(R) ** 3

def induced_isoscalar_e1_kernel(A, e, R, deltaE0, ri, rj):
    return sp.factor(ivgmr_coefficient(A, e, R, deltaE0) *
                     (ivgmr_one_body_radial(ri, R) +
                      ivgmr_two_body_radial(ri, rj, R)))

assert induced_isoscalar_e1_kernel(67, 1, 1, 20, 1, 1) == Q(33, 20)

print({
    "isospin_casimir_half": isospin_casimir(Q(1, 2)),
    "tz_flip_sum": Q(-1, 2) + Q(1, 2),
    "dilation_stiffness_67": dilation_spring_stiffness(poincare_mass_casimir(Q(67))),
    "ivgmr_kernel_A67": induced_isoscalar_e1_kernel(67, 1, 1, 20, 1, 1),
})

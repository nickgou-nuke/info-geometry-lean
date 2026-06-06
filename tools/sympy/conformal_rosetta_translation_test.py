import sympy as sp
from sympy import Matrix, eye, zeros


def comm(a: Matrix, b: Matrix) -> Matrix:
    return a * b - b * a


def mobius_action(m: Matrix, z):
    return sp.simplify((m[0, 0] * z + m[0, 1]) / (m[1, 0] * z + m[1, 1]))


def action_eq(lhs, rhs) -> bool:
    return sp.simplify(lhs - rhs) == 0


def is_zero(m: Matrix) -> bool:
    return m.equals(zeros(*m.shape))


z, lam, lam1, lam2, time = sp.symbols("z lam lam1 lam2 time", real=True)

# Conformal sl2 generators.
P = Matrix([[0, 1], [0, 0]])
D = Matrix([[sp.Rational(1, 2), 0], [0, -sp.Rational(1, 2)]])
K = Matrix([[0, 0], [1, 0]])

def boost(l):
    return Matrix([[sp.exp(l / 2), 0], [0, sp.exp(-l / 2)]])

# Projective generators.
T = Matrix([[1, 1], [0, 1]])
S = Matrix([[0, -1], [1, 0]])

# Klein four projective packet.
neg = Matrix([[-1, 0], [0, 1]])
inv = Matrix([[0, 1], [1, 0]])
neg_inv = neg * inv

# Conformal inversion generator from the null-pair lane.
u = Matrix([[0, 1], [0, 0]])
v = Matrix([[0, 0], [1, 0]])
J = u - v

# Rindler/light-cone readout.
radius = sp.symbols("radius", positive=True)
x_plus = radius * sp.exp(time)
x_minus = radius * sp.exp(-time)

checks = {
    # rapidity / boost
    "boost_adds_rapidity": is_zero(boost(lam1) * boost(lam2) - boost(lam1 + lam2)),
    "exp/log readout": sp.simplify(sp.exp(lam) * sp.exp(time) - sp.exp(time + lam)) == 0,
    "Rindler shift in x_plus": sp.simplify(sp.exp(lam) * x_plus - radius * sp.exp(time + lam)) == 0,

    # conformal sl2
    "P^2 = 0": is_zero(P**2),
    "D trace = 0": D.trace() == 0,
    "K^2 = 0": is_zero(K**2),
    "[D,P] = P": is_zero(comm(D, P) - P),
    "[D,K] = -K": is_zero(comm(D, K) + K),
    "[P,K] = 2D": is_zero(comm(P, K) - 2 * D),

    # Möbius / projective
    "T(z)=z+1": action_eq(mobius_action(T, z), z + 1),
    "S(z)=-1/z": action_eq(mobius_action(S, z), -1 / z),
    "S^2 projectively=id": sp.simplify(mobius_action(S * S, z) - z) == 0,

    # Klein V4
    "neg(z)=-z": action_eq(mobius_action(neg, z), -z),
    "inv(z)=1/z": action_eq(mobius_action(inv, z), 1 / z),
    "neg_inv(z)=-1/z": action_eq(mobius_action(neg_inv, z), -1 / z),
    "V4 commute": action_eq(mobius_action(neg * inv, z), mobius_action(inv * neg, z)),

    # Conformal inversion / null-pair
    "u^2 = 0": is_zero(u**2),
    "v^2 = 0": is_zero(v**2),
    "u v + v u = I": is_zero(u * v + v * u - eye(2)),
    "J^2 = -I": is_zero(J**2 + eye(2)),
    "J u J = v": is_zero(J * u * J - v),
    "J v J = u": is_zero(J * v * J - u),
}


print("Rosetta table: SymPy -> Lean")
rows = [
    ("rapidity boost", "B(λ) = diag(exp(λ/2), exp(-λ/2))",
     "Dynamics.RapiditySpace.componentAReal"),
    ("Rindler flow", "x_± = r exp(±t)",
     "Dynamics.RindlerWedge.rindler_flow_is_time_translation"),
    ("conformal inversion", "J = u - v, J^2 = -I",
     "Clifford.ConformalReflection55.J_sq"),
    ("Möbius inversion", "S(z) = -1/z",
     "Clifford.DiscreteMoebiusGroup.moebius_S_action"),
    ("Klein V4", "{id, -z, 1/z, -1/z}",
     "Clifford.DiscreteMoebiusGroup.kleinV4_commute_on_actions"),
    ("conformal sl2", "{P, D, K}",
     "Canonical.ConformalSL2GeneratorBridge.P / D / K"),
]
for a, b, c in rows:
    print(f"  {a:20s} | {b:34s} | {c}")

print("\nChecks:")
for key, value in checks.items():
    print(f"  {key}: {value}")

print("\nInterpretation:")
print("  rapidity/log lane = additive hyperbolic flow")
print("  inversion lane    = origin <-> infinity swap")
print("  projective lane   = Möbius chart readout")
print("  Op -> 1/Op        = reciprocal projective readout, not literal inversion unless Op is invertible")
print(f"OVERALL: {all(checks.values())}")

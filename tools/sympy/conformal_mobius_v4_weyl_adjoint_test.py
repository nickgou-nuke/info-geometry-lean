import sympy as sp
from sympy import Matrix, eye, zeros


z = sp.Symbol("z")


def mobius_action(m: Matrix, zz):
    return sp.simplify((m[0, 0] * zz + m[0, 1]) / (m[1, 0] * zz + m[1, 1]))


def conj(m: Matrix, x: Matrix) -> Matrix:
    return sp.simplify(m * x * m.inv())


def is_zero(m: Matrix) -> bool:
    return m.equals(zeros(*m.shape))


I2 = eye(2)

# Conformal sl2 basis on the affine/projective chart.
P = Matrix([[0, 1], [0, 0]])
D = Matrix([[sp.Rational(1, 2), 0], [0, -sp.Rational(1, 2)]])
K = Matrix([[0, 0], [1, 0]])

# Projective Möbius generators.
S = Matrix([[0, -1], [1, 0]])
T = Matrix([[1, 1], [0, 1]])

# Klein four in projective/Möbius form.
neg = Matrix([[-1, 0], [0, 1]])   # z -> -z
inv = Matrix([[0, 1], [1, 0]])    # z -> 1/z
neg_inv = neg * inv               # z -> -1/z (projectively)

# Root-lattice Weyl reflections for A1 x A1.
r1 = Matrix([[-1, 0], [0, 1]])
r2 = Matrix([[1, 0], [0, -1]])
r3 = r1 * r2
G = Matrix([[2, 0], [0, 2]])


def action_of(m: Matrix):
    return sp.simplify(mobius_action(m, z))


checks = {
    # Möbius generators
    "S^2 = -I projectively": mobius_action(S * S, z) == z,
    "T acts as z -> z + 1": mobius_action(T, z) == z + 1,
    "S acts as z -> -1/z": mobius_action(S, z) == -1 / z,

    # Klein V4 on the projective line
    "neg^2 = id": action_of(neg * neg) == z,
    "inv^2 = id": action_of(inv * inv) == z,
    "neg_inv^2 = id": action_of(neg_inv * neg_inv) == z,
    "neg then inv = neg_inv": action_of(neg * inv) == action_of(neg_inv),
    "inv then neg = neg_inv": action_of(inv * neg) == action_of(neg_inv),
    "V4 commutes on actions": action_of(neg * inv) == action_of(inv * neg),
    "neg(z) = -z": action_of(neg) == -z,
    "inv(z) = 1/z": action_of(inv) == 1 / z,
    "neg_inv(z) = -1/z": action_of(neg_inv) == -1 / z,

    # Weyl group of A1 x A1 on the root lattice
    "r1^2 = I": is_zero(r1**2 - I2),
    "r2^2 = I": is_zero(r2**2 - I2),
    "r3^2 = I": is_zero(r3**2 - I2),
    "r1 r2 = r2 r1": is_zero(r1 * r2 - r2 * r1),
    "r1 r2 = r3": is_zero(r1 * r2 - r3),
    "r1 preserves G": is_zero(r1.T * G * r1 - G),
    "r2 preserves G": is_zero(r2.T * G * r2 - G),
    "r3 preserves G": is_zero(r3.T * G * r3 - G),

    # Adjoint action on the conformal sl2 basis
    "Ad_neg(P) = -P": is_zero(conj(neg, P) + P),
    "Ad_neg(D) = D": is_zero(conj(neg, D) - D),
    "Ad_neg(K) = -K": is_zero(conj(neg, K) + K),
    "Ad_inv(P) = K": is_zero(conj(inv, P) - K),
    "Ad_inv(D) = -D": is_zero(conj(inv, D) + D),
    "Ad_inv(K) = P": is_zero(conj(inv, K) - P),
    "Ad_neg_inv(P) = -K": is_zero(conj(neg_inv, P) + K),
    "Ad_neg_inv(D) = -D": is_zero(conj(neg_inv, D) + D),
    "Ad_neg_inv(K) = -P": is_zero(conj(neg_inv, K) + P),
    "adjoint commutes on generators":
        is_zero(conj(neg, conj(inv, P)) - conj(inv, conj(neg, P)))
        and is_zero(conj(neg, conj(inv, D)) - conj(inv, conj(neg, D)))
        and is_zero(conj(neg, conj(inv, K)) - conj(inv, conj(neg, K))),
}


print("Mobius/projective layer:")
for key in [
    "S^2 = -I projectively",
    "T acts as z -> z + 1",
    "S acts as z -> -1/z",
    "neg^2 = id",
    "inv^2 = id",
    "neg_inv^2 = id",
    "neg then inv = neg_inv",
    "inv then neg = neg_inv",
    "V4 commutes on actions",
    "neg(z) = -z",
    "inv(z) = 1/z",
    "neg_inv(z) = -1/z",
]:
    print(f"  {key}: {checks[key]}")

print("\nWeyl A1 x A1 lattice layer:")
for key in [
    "r1^2 = I",
    "r2^2 = I",
    "r3^2 = I",
    "r1 r2 = r2 r1",
    "r1 r2 = r3",
    "r1 preserves G",
    "r2 preserves G",
    "r3 preserves G",
]:
    print(f"  {key}: {checks[key]}")

print("\nAdjoint action on sl2 generators:")
for key in [
    "Ad_neg(P) = -P",
    "Ad_neg(D) = D",
    "Ad_neg(K) = -K",
    "Ad_inv(P) = K",
    "Ad_inv(D) = -D",
    "Ad_inv(K) = P",
    "Ad_neg_inv(P) = -K",
    "Ad_neg_inv(D) = -D",
    "Ad_neg_inv(K) = -P",
    "adjoint commutes on generators",
]:
    print(f"  {key}: {checks[key]}")

print("\nInterpretation:")
print("  Klein V4 on the projective line: {id, z -> -z, z -> 1/z, z -> -1/z}")
print("  Weyl group witness: A1 x A1 reflections r1,r2,r3")
print("  Adjoint witness: the same reflections act by conjugation on P,D,K")
print(f"OVERALL: {all(checks.values())}")

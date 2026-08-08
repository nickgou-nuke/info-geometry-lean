import sympy as sp


sqrt5 = sp.sqrt(5)
phi = (1 + sqrt5) / 2
k = sp.symbols("k")
l = sp.symbols("l")

assert sp.simplify(phi**2 - phi - 1) == 0
assert sp.simplify(sp.log(phi) - sp.log(phi)) == 0

phi_distance_0 = phi**0
assert sp.simplify(phi_distance_0 - 1) == 0

phi_distance_k = phi ** (-k)
phi_distance_succ = phi ** (-(k + 1))
assert sp.simplify(phi_distance_succ - phi_distance_k / phi) == 0

phi_distance_l = phi ** (-l)
phi_distance_add = phi ** (-(k + l))
assert sp.simplify(phi_distance_add - phi_distance_k * phi_distance_l) == 0

golden_energy = sp.log(phi)
assert sp.simplify((k + l) * golden_energy - (k * golden_energy + l * golden_energy)) == 0
assert sp.simplify(1 * golden_energy - golden_energy) == 0


def golden_prime_class(p: int) -> str:
    residue = p % 5
    if residue == 0:
        return "ramified"
    if residue in (1, 4):
        return "split"
    return "inert"


assert golden_prime_class(5) == "ramified"
assert golden_prime_class(11) == "split"
assert golden_prime_class(19) == "split"
assert golden_prime_class(3) == "inert"
assert golden_prime_class(13) == "inert"

a, b, c, d = sp.symbols("a b c d", integer=True)


def golden_mul(x, y):
    xa, xb = x
    ya, yb = y
    return (xa * ya + xb * yb, xa * yb + xb * ya + xb * yb)


def golden_add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def golden_conj(x):
    return (x[0] + x[1], -x[1])


def golden_norm(x):
    return x[0] ** 2 + x[0] * x[1] - x[1] ** 2


def golden_eval(x):
    return x[0] + x[1] * phi


one = (1, 0)
varphi = (0, 1)
x = (a, b)
y = (c, d)

assert golden_mul(varphi, varphi) == golden_add(varphi, one)
assert golden_conj(golden_conj(x)) == x
assert sp.simplify(golden_norm(golden_conj(x)) - golden_norm(x)) == 0
assert sp.simplify(golden_norm(golden_mul(x, y)) - golden_norm(x) * golden_norm(y)) == 0
assert sp.simplify(golden_eval(golden_mul(x, y)) - golden_eval(x) * golden_eval(y)) == 0

print("PenroseArithmetic.py: golden ring, splitting, and phi-adic identities verified")

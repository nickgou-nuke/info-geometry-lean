import sympy as sp


def coord(bit):
    return sp.Integer(1) if bit else sp.Integer(0)


def occupation_lane(e, x):
    return (1 - e) + e * x


def parity_lane(e):
    return 1 - 2 * e


def graded_lane(e, x):
    return sp.expand(parity_lane(e) * occupation_lane(e, x))


def boundary_local_graded(bit, x):
    return graded_lane(coord(bit), x)


x0, x1, x2 = sp.symbols("x0 x1 x2")

assert coord(False) ** 2 == coord(False)
assert coord(True) ** 2 == coord(True)

assert occupation_lane(coord(False), x0) == 1
assert occupation_lane(coord(True), x0) == x0
assert parity_lane(coord(False)) == 1
assert parity_lane(coord(True)) == -1
assert boundary_local_graded(False, x0) == 1
assert boundary_local_graded(True, x0) == -x0


def boundary_graded_product(bits, xs):
    out = 1
    for bit, x in zip(bits, xs):
        out *= boundary_local_graded(bit, x)
    return sp.expand(out)


bits = [True, False, True]
assert boundary_graded_product(bits, [x0, x1, x2]) == sp.expand(x0 * x2)

# Boolean trace over the UHF diagonal coordinates recovers the finite
# graded determinant.
trace = 0
for b0 in (False, True):
    for b1 in (False, True):
        for b2 in (False, True):
            trace += boundary_graded_product([b0, b1, b2], [x0, x1, x2])

assert sp.expand(trace) == sp.expand((1 - x0) * (1 - x1) * (1 - x2))

print("SymbolicLaneUHFBridge.py: symbolic idempotents realized as UHF boundary coordinates")

import sympy as sp


def diag_embed(values):
    out = []
    for value in values:
        out.extend([value, value])
    return out


def graded_factor(xs):
    return sp.expand(sp.prod(1 - x for x in xs))


def constant_observable(level, value):
    return [value] * (2**level)


x2, x3, x5, x7 = sp.symbols("x2 x3 x5 x7")
xs = [x2, x3, x5]
z = graded_factor(xs)
z_next = graded_factor(xs + [x7])

stage = constant_observable(len(xs), z)
embedded_stage = diag_embed(stage)
same_constant_next_stage = constant_observable(len(xs) + 1, z)
updated_next_stage = constant_observable(len(xs) + 1, z_next)
local_update = constant_observable(len(xs) + 1, 1 - x7)

assert embedded_stage == same_constant_next_stage
assert updated_next_stage == [sp.expand(a * b) for a, b in zip(same_constant_next_stage, local_update)]
assert sp.simplify(z_next - z * (1 - x7)) == 0

# Boson/graded cancellation persists as a constant cylinder observable.
bosonic_z = sp.prod(1 / (1 - x) for x in xs)
cancelled = constant_observable(len(xs), sp.simplify(bosonic_z * z))

assert cancelled == constant_observable(len(xs), 1)

print("FockUHFBridge.py: finite Fock factors embedded as UHF cylinder observables")

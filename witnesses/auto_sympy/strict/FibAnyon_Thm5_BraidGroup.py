import sympy as sp

q, a, s = sp.symbols("q a s")
F = sp.Matrix([[a, s], [s, -a]])
R = sp.Matrix([[q**4, 0], [0, q**7]])
B = F * R * F
b1, b2, b3 = R, B, R

relations = [
    q**4 - q**3 + q**2 - q + 1,
    a - (q**2 - q**3),
    s**2 - a,
]
gb = sp.groebner(relations, q, a, s, order="lex")

def reduce_entries(matrix):
    return [sp.factor(gb.reduce(sp.expand(entry))[1]) for entry in matrix]

checks = {
    "far_commutativity": reduce_entries(b1 * b3 - b3 * b1),
    "artin_relation": reduce_entries(b1 * b2 * b1 - b2 * b1 * b2),
}

for name, remainders in checks.items():
    for idx, rem in enumerate(remainders):
        print(f"{name}_{idx} = {rem}")
        assert rem == 0, (name, idx, rem)

print("strict_fibonacci_braid_group_witness = ok")

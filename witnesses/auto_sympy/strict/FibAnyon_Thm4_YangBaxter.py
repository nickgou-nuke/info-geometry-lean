import sympy as sp

# Exact Fibonacci braid witness.
# q is a primitive 10th root with cyclotomic relation Phi_10(q) = 0.
# a = 1/phi is tied to q by a = q^2 - q^3, and s^2 = a.
q, a, s = sp.symbols("q a s")
F = sp.Matrix([[a, s], [s, -a]])
R = sp.Matrix([[q**4, 0], [0, q**7]])  # diag(exp(4*pi*i/5), exp(-3*pi*i/5))
B = F * R * F

relations = [
    q**4 - q**3 + q**2 - q + 1,
    a - (q**2 - q**3),
    s**2 - a,
]
gb = sp.groebner(relations, q, a, s, order="lex")
remainders = [sp.factor(gb.reduce(sp.expand(entry))[1]) for entry in (R * B * R - B * R * B)]

for idx, rem in enumerate(remainders):
    print(f"yang_baxter_remainder_{idx} = {rem}")
    assert rem == 0, (idx, rem)

print("strict_fibonacci_yang_baxter_witness = ok")

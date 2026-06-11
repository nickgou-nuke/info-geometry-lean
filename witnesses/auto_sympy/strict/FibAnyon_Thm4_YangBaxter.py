import sympy as sp

# Exact Fibonacci braid witness using hardcoded polynomial factorizations.
q, a, s = sp.symbols("q a s")
phi10 = q**4 - q**3 + q**2 - q + 1


def poly_zero(expr):
    return sp.Poly(sp.expand(expr), q, a, s).is_zero


tau_q = q**2 - q**3
norm_left = tau_q**2 + tau_q - 1
norm_right = (q**2 - q - 1) * phi10

artin_left = tau_q**2 * (q**4 - q**7) ** 2 + q**11
artin_right = q**11 * (q**5 - q**4 - q**3 - q**2 + 2 * q + 1) * phi10

assert poly_zero(norm_left - norm_right), "norm factorization"
assert poly_zero(artin_left - artin_right), "Artin scalar factorization"

F = sp.Matrix([[a, s], [s, -a]])
R = sp.Matrix([[q**4, 0], [0, q**7]])
B = F * R * F
D = sp.Matrix(R * B * R - B * R * B)

norm = a**2 + s**2 - 1
artin = a**2 * (q**4 - q**7) ** 2 + q**11
entry_reductions = [
    (
        -q**7
        * (
            3 * a**2 * q**8
            - 3 * a**2 * q**11
            + a**2 * q**14
            + s**2 * q**11
            - q**8
            + q**11
        ),
        -(a - 1) * (a + 1) * (q**4 - q**7),
    ),
    (-2 * a * s * q**11 * (q**4 - q**7), -a * s * (q**4 - q**7)),
    (-2 * a * s * q**11 * (q**4 - q**7), -a * s * (q**4 - q**7)),
    (
        -q**4
        * (
            a**2 * q**8
            - 3 * a**2 * q**11
            + 3 * a**2 * q**14
            + s**2 * q**11
            + q**11
            - q**14
        ),
        (a - 1) * (a + 1) * (q**4 - q**7),
    ),
]

for idx, (entry, (c_norm, c_artin)) in enumerate(zip(D, entry_reductions, strict=True)):
    residual = sp.expand(entry - (c_norm * norm + c_artin * artin))
    print(f"yang_baxter_factorization_{idx} = {residual}")
    assert poly_zero(residual), (idx, residual)

print("strict_fibonacci_yang_baxter_witness = ok")

# Exact-rational Sage certificate for Jensen inverse-iteration inclusion.
# Verifies Jensen's quadratic root formula in QQ(sqrt(radicand)) and the
# interval readout for a monotone rational model sequence.

QQ = RationalField()
P.<x> = PolynomialRing(QQ)

def jensen_polynomial(b, j, z):
    return (-(b[j - 1] - b[j]) * z**2
            + b[j - 1] * (b[j - 2] - b[j]) * z
            - b[j - 1] * b[j] * (b[j - 2] - b[j - 1]))

def accelerated_radius_formula(b, j):
    radicand = ((b[j - 2] - b[j])**2
                - 4 * (b[j - 1] - b[j]) * (b[j - 2] - b[j - 1]) * (b[j] / b[j - 1]))
    K.<s> = NumberField(x^2 - QQ(radicand))
    bK = {k: K(v) for k, v in b.items()}
    delta = bK[j - 1] * ((bK[j - 2] - bK[j]) - s) / (2 * (bK[j - 1] - bK[j]))
    return K, delta

h = QQ(1) / QQ(5)
q = QQ(1) / QQ(3)
b = {j: h + q**j for j in range(1, 8)}

for j in range(3, 8):
    K, delta = accelerated_radius_formula(b, j)
    bK = {k: K(v) for k, v in b.items()}
    assert jensen_polynomial(bK, j, delta) == 0
    assert K(h) <= delta <= K(b[j])
    mu = K(QQ(7) / QQ(2))
    lam = mu + K(h)
    assert mu - delta <= lam <= mu + delta

print("jensen inverse-iteration inclusion Sage certificate: ok")

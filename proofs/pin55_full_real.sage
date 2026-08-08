#!/usr/bin/env sage
# Exact SageMath certificate for the real Cl(5,5) coordinate reflections.

R = QQ
I2 = identity_matrix(R, 2)
X = matrix(R, [[0, 1], [1, 0]])
Y = matrix(R, [[0, 1], [-1, 0]])
Z = diagonal_matrix(R, [1, -1])

def kron_all(parts):
    out = matrix(R, [[1]])
    for part in parts:
        out = out.tensor_product(part)
    return out

def gamma(local, i):
    return kron_all([Z] * i + [local] + [I2] * (4 - i))

gammas = [gamma(X, i) for i in range(5)] + [gamma(Y, i) for i in range(5)]
signs = [1] * 5 + [-1] * 5
I32 = identity_matrix(R, 32)
eta = diagonal_matrix(R, signs)

for a in range(10):
    for b in range(10):
        expected = 2 * signs[a] * I32 if a == b else zero_matrix(R, 32)
        assert gammas[a] * gammas[b] + gammas[b] * gammas[a] == expected

reflections = []
for a in range(10):
    ga = gammas[a]
    ga_inv = signs[a] * ga
    r = zero_matrix(R, 10)
    for b in range(10):
        image = -ga * gammas[b] * ga_inv
        for c in range(10):
            r[c, b] = (gammas[c] * image).trace() / (32 * signs[c])
    expected = identity_matrix(R, 10)
    expected[a, a] = -1
    assert r == expected
    assert r.transpose() * eta * r == eta
    assert r.det() == -1
    reflections.append(r)

# PBW monomials give the expected 2^10-dimensional matrix basis.
monomials = []
for mask in range(2^10):
    value = I32
    for a in range(10):
        if mask & (1 << a):
            value *= gammas[a]
    monomials.append(vector(R, value.list()))
assert matrix(R, monomials).rank() == 2^10

images = set()
kernel_count = 0
for mask in range(2^10):
    image = identity_matrix(R, 10)
    for a in range(10):
        if mask & (1 << a):
            image *= reflections[a]
    images.add(tuple(image.list()))
    if image == identity_matrix(R, 10):
        kernel_count += 2
assert len(images) == 2^10
assert kernel_count == 2

print("pin55_full_real.sage: PASS")
print("Cl(5,5) matrix algebra dimension:", 2^10)
print("coordinate reflections:", len(reflections))
print("metric inertia: (5,5)")
print("signed monomial image order:", len(images))
print("signed monomial kernel order:", kernel_count)

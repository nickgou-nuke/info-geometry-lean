# Exact finite-core check for the Branman countable-Stone layer.
from math import factorial


for m in range(1, 7):
    G = SymmetricGroup(m)
    assert G.order() == factorial(m)

modulus = 5
labels = {1, modulus - 1}


def adj(g, h):
    return ((h - g) % modulus) in labels


for f in labels:
    assert (-f) % modulus in labels

for g in range(modulus):
    for h in range(modulus):
        assert adj(g, h) == adj(h, g)
        for k in range(modulus):
            assert adj(g, h) == adj((k + g) % modulus, (k + h) % modulus)

print("branman countable Stone finite core Sage check: ok")

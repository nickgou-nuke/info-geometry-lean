var('x1 x2 x3 a1 a2 a3 r')

x = vector([x1, x2, x3])
a = vector([a1, a2, a3])

def I(v):
    v1, v2, v3 = v[0], v[1], v[2]
    n_sq = (v1 - a1)^2 + (v2 - a2)^2 + (v3 - a3)^2
    return a + (r^2 / n_sq) * (v - a)

Ix = I(x)
IIx = I(Ix)

simp_IIx = []
for i in range(3):
    simp_IIx.append(IIx[i].full_simplify())

res = vector(simp_IIx)

print("Original x:", x)
print("Simplified I(I(x)):", res)

if res == x:
    print("Proof successful: I(I(x)) = x")
else:
    print("Proof failed")

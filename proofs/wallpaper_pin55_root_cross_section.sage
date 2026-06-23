# Exact-rational Sage certificate for the wallpaper/Pin(5,5) root cross-section.

itpermutations = __import__('itertools').permutations
itproduct = __import__('itertools').product

T = matrix(QQ, [[0,-1],[1,0]])
G = matrix(QQ, [[1,0],[0,-1]])
I2 = identity_matrix(QQ, 2)
D4 = [I2, T, -I2, -T, G, T*G, -G, -T*G]
B2 = [vector(QQ, v) for v in [(1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1),(1,-1),(-1,1)]]
D5 = set()
for i, j in itpermutations(range(5), int(2)):
    if i == j: continue
    for si, sj in itproduct([1,-1], repeat=int(2)):
        v = [0]*5; v[i] = si; v[j] = sj; D5.add(tuple(v))
LIFTS = [(1,0,1,0,0),(-1,0,1,0,0),(0,1,1,0,0),(0,-1,1,0,0),
         (1,1,0,0,0),(-1,-1,0,0,0),(1,-1,0,0,0),(-1,1,0,0,0)]
WEYL = [
    identity_matrix(QQ,5),
    matrix(QQ, [[0,-1,0,0,0],[1,0,0,0,0],[0,0,-1,0,0],[0,0,0,1,0],[0,0,0,0,1]]),
    diagonal_matrix(QQ, [-1,-1,1,1,1]),
    matrix(QQ, [[0,1,0,0,0],[-1,0,0,0,0],[0,0,-1,0,0],[0,0,0,1,0],[0,0,0,0,1]]),
    diagonal_matrix(QQ, [1,-1,-1,1,1]),
    matrix(QQ, [[0,1,0,0,0],[1,0,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]]),
    diagonal_matrix(QQ, [-1,1,-1,1,1]),
    matrix(QQ, [[0,-1,0,0,0],[-1,0,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]])]
assert all(l in D5 for l in LIFTS)
assert [l[:2] for l in LIFTS] == [tuple(v) for v in B2]
b2set = set(tuple(v) for v in B2)
for M,W in zip(D4, WEYL):
    assert W.transpose()*W == identity_matrix(QQ,5)
    assert W[0:2,0:2] == M
    for r,l in zip(B2,LIFTS):
        assert tuple(M*r) in b2set
        image = W*vector(QQ,l)
        assert tuple(image) in D5
        assert tuple(image[:2]) == tuple(M*r)
plane = {v[:2] for v in D5 if v[2:] == (0,0,0)}
assert plane == {(1,1),(1,-1),(-1,1),(-1,-1)}
print("wallpaper Pin55 root cross-section Sage certificate: ok")

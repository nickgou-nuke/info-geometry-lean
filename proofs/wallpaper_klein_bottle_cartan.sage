# Exact-rational Sage certificate for Klein-compatible wallpaper symmetries.

T = matrix(QQ, [[0, -1], [1, 0]])
G = matrix(QQ, [[1, 0], [0, -1]])
I = identity_matrix(QQ, 2)
D4 = [I, T, -I, -T, G, T*G, -G, -T*G]
eta55 = diagonal_matrix(QQ, [1,1,1,1,1,-1,-1,-1,-1,-1])
assert eta55.transpose() == eta55
assert eta55 * eta55 == identity_matrix(QQ, 10)
assert T*T == -I
assert G*G == I
assert G*T == -T*G
for S in D4:
    assert S.transpose() * S == I
    assert S*T == T*S or S*T == -T*S
    assert S*(T*T) == -S
assert len(set(tuple(S.list()) for S in D4)) == 8
for A in D4:
    for B in D4:
        assert tuple((A*B).list()) in set(tuple(S.list()) for S in D4)
print("wallpaper Klein-bottle Cartan Sage certificate: ok")

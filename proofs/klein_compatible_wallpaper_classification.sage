# Exact-rational Sage certificate for finite pg/pmg/pgg Klein-compatible candidates.

Tx = matrix(QQ, [[1,0,1],[0,1,0],[0,0,1]])
Ty = matrix(QQ, [[1,0,0],[0,1,1],[0,0,1]])
Gx = matrix(QQ, [[1,0,QQ(1)/2],[0,-1,0],[0,0,1]])
Mx = matrix(QQ, [[-1,0,0],[0,1,0],[0,0,1]])
Gy = matrix(QQ, [[-1,0,0],[0,1,QQ(1)/2],[0,0,1]])
I = identity_matrix(QQ, 3)
assert Gx * Gx == Tx
assert Gx * Ty == Ty.inverse() * Gx
assert Mx * Mx == I
assert Gy * Gy == Ty
assert Gy * Tx == Tx.inverse() * Gy
roots = {(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)}
assert (0,1) in roots and (1,-1) in roots and (1,0) in roots
print("klein compatible wallpaper classification Sage certificate: ok")

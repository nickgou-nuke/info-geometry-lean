#!/usr/bin/env sage
Tx = Matrix(QQ, [[0,1],[1,0]])
Ty = Matrix(QQ, [[1,0],[0,-1]])
I = identity_matrix(QQ, 2)
minusI = -I
Txy = Tx*Ty
assert Tx*Tx == I
assert Ty*Ty == I
assert Tx*Ty == -(Ty*Tx)
assert Tx*Ty == minusI*(Ty*Tx)
assert Txy*Txy == minusI

def glide(p):
    x,y = p
    return (x+1, -y)
def glideInv(p):
    x,y = p
    return (x-1, -y)
def yLoop(p):
    x,y = p
    return (x, y+2)
def yLoopInv(p):
    x,y = p
    return (x, y-2)

for x in range(-3,4):
    for y in range(-3,4):
        p = (QQ(x), QQ(y))
        assert glide(glideInv(p)) == p
        assert glideInv(glide(p)) == p
        assert glide(yLoop(glideInv(p))) == yLoopInv(p)
        assert glide(yLoop(glideInv(yLoop(p)))) == p

print("brillouin Klein bottle manifold Sage certificate: ok")

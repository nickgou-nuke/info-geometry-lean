Tx = matrix(QQ, [[0, 1], [1, 0]])
Ty = matrix(QQ, [[1, 0], [0, -1]])

assert Tx * Ty == -(Ty * Tx), "Tx * Ty == -(Ty * Tx) failed"
assert (Tx * Ty)^2 == -matrix.identity(2), "(Tx * Ty)^2 == -I failed"
print("Passed: Tx * Ty == -(Ty * Tx) and (Tx * Ty)^2 == -I")

def trans0(a, x):
    res = copy(x)
    res[0] = res[0] + a
    return res

def affineReflect0(x):
    res = copy(x)
    res[0] = -res[0]
    return res

var('a')
x_vars = [var('x_%d' % i) for i in range(10)]
x = vector(SR, x_vars)

lhs = affineReflect0(trans0(a, affineReflect0(x)))
rhs = trans0(-a, x)

assert lhs == rhs, "Klein bottle relation failed"
print("Passed: affineReflect0(trans0(a, affineReflect0(x))) == trans0(-a, x)")
print("All Brillouin-Klein bottle proofs passed successfully.")

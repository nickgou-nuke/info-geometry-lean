import sympy as sp

def verify_fibonacci_ring_and_block():
    # 1. Verify FibonacciRingModel identities
    x1, x2, y1, y2, z1, z2 = sp.symbols('x1 x2 y1 y2 z1 z2', integer=True)
    
    def mul(a, b):
        return (a[0]*b[0] + a[1]*b[1], a[0]*b[1] + a[1]*b[0] + a[1]*b[1])
    
    def add(a, b):
        return (a[0]+b[0], a[1]+b[1])
    
    one = (1, 0)
    tau = (0, 1)
    x = (x1, x2)
    y = (y1, y2)
    z = (z1, z2)
    
    # tau * tau = tau + one
    assert mul(tau, tau) == add(tau, one)
    # commutativity
    assert sp.simplify(mul(x, y)[0] - mul(y, x)[0]) == 0
    assert sp.simplify(mul(x, y)[1] - mul(y, x)[1]) == 0
    # associativity
    assert sp.simplify(mul(mul(x, y), z)[0] - mul(x, mul(y, z))[0]) == 0
    assert sp.simplify(mul(mul(x, y), z)[1] - mul(x, mul(y, z))[1]) == 0
    # left distributivity
    assert sp.simplify(mul(x, add(y, z))[0] - add(mul(x, y), mul(x, z))[0]) == 0
    assert sp.simplify(mul(x, add(y, z))[1] - add(mul(x, y), mul(x, z))[1]) == 0
    # right distributivity
    assert sp.simplify(mul(add(x, y), z)[0] - add(mul(x, z), mul(y, z))[0]) == 0
    assert sp.simplify(mul(add(x, y), z)[1] - add(mul(x, z), mul(y, z))[1]) == 0
    # tensorTau compatibility: (x2, x1 + x2) == mul(x, tau)
    assert sp.simplify(x2 - mul(x, tau)[0]) == 0
    assert sp.simplify((x1 + x2) - mul(x, tau)[1]) == 0

    # 2. Verify 2x2 block insertion for identity matrix
    d = 4
    I2 = sp.eye(2)
    for a in range(d):
        for b in range(d):
            if a == b:
                continue
            M = sp.zeros(d, d)
            for i in range(d):
                for j in range(d):
                    if i == a:
                        if j == a: M[i, j] = I2[0, 0]
                        elif j == b: M[i, j] = I2[0, 1]
                        else: M[i, j] = 0
                    elif i == b:
                        if j == a: M[i, j] = I2[1, 0]
                        elif j == b: M[i, j] = I2[1, 1]
                        else: M[i, j] = 0
                    else:
                        M[i, j] = 1 if i == j else 0
            assert M == sp.eye(d)
    print("All SymPy verifications passed!")

if __name__ == "__main__":
    verify_fibonacci_ring_and_block()

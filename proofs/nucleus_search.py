import sympy as sp

# Basis vectors mapping to SplitOct components
# e0: a.re
# e1: a.imI
# e2: a.imJ
# e3: a.imK
# e4: b.re
# e5: b.imI
# e6: b.imJ
# e7: b.imK

def qmul(x, y):
    re = x[0]*y[0] - x[1]*y[1] - x[2]*y[2] - x[3]*y[3]
    imI = x[0]*y[1] + x[1]*y[0] + x[2]*y[3] - x[3]*y[2]
    imJ = x[0]*y[2] - x[1]*y[3] + x[2]*y[0] + x[3]*y[1]
    imK = x[0]*y[3] + x[1]*y[2] - x[2]*y[1] + x[3]*y[0]
    return [re, imI, imJ, imK]

def qadd(x, y):
    return [x[0]+y[0], x[1]+y[1], x[2]+y[2], x[3]+y[3]]

def qsub(x, y):
    return [x[0]-y[0], x[1]-y[1], x[2]-y[2], x[3]-y[3]]

def qstar(x):
    return [x[0], -x[1], -x[2], -x[3]]

def split_mul(x, y):
    xa, xb = x[:4], x[4:]
    ya, yb = y[:4], y[4:]
    za = qadd(qmul(xa, ya), qmul(qstar(yb), xb))
    zb = qadd(qmul(yb, xa), qmul(xb, qstar(ya)))
    return za + zb

basis = []
for i in range(8):
    v = [0]*8
    v[i] = 1
    basis.append(v)

b = sp.symbols('b0:8')

for i in range(1, 8):
    for j in range(1, 8):
        ei = basis[i]
        ej = basis[j]
        # (ei * b) * ej - ei * (b * ej)
        eib = split_mul(ei, b)
        eib_ej = split_mul(eib, ej)
        bej = split_mul(b, ej)
        ei_bej = split_mul(ei, bej)
        
        diff = [sp.simplify(eib_ej[k] - ei_bej[k]) for k in range(8)]
        
        for k in range(8):
            if diff[k] != 0:
                print(f"i={i}, j={j}, k={k} -> diff = {diff[k]}")

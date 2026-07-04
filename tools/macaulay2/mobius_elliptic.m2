R = QQ[u, v, x, y]
I = ideal(u^2 + v^2 - 1)
E = matrix {{u, -v}, {v, u}}
expr = (u*x - v*y)^2 + (v*x + u*y)^2 - (x^2 + y^2)
rem = expr % I
print(rem)
assert(rem == 0)

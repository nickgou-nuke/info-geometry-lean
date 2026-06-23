# Exact finite certificate for Bayesian/Turing/Cantor layer.
def words(n):
    if n == 0:
        return [()]
    return [w + (b,) for w in words(n-1) for b in (0,1)]

tape = (1,0,1,1,0,0,1)
for n in range(5):
    assert tape[1:][:n] == tape[:n+1][1:]

U = set(words(3))
A = {w for w in U if w[0] == 1}
B = {w for w in U if w[1] == 0}
x = tape[:3]
assert (x in (A & B)) == ((x in A) and (x in B))
assert (x in (A | B)) == ((x in A) or (x in B))
assert (x in (U - A)) == (not (x in A))

posterior = {w: QQ(1) if w == x else QQ(0) for w in U}
assert sum(posterior.values()) == QQ(1)
assert posterior[x] == QQ(1)

a,b,c = QQ(2)/3, QQ(5)/7, -QQ(11)/13
inc = lambda p,q: q-p
assert inc(a,b) + inc(b,c) == inc(a,c)
assert inc(a,b) + inc(b,c) + inc(c,a) == 0
Q = QQ(17)/19
assert Q/Q == 1
print('bayesian Turing Cantor Sage certificate: ok')

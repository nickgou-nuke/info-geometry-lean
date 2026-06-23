# Exact finite certificate for UHF Boolean projection / Cantor prefix bridge.
def words(n):
    if n == 0:
        return [()]
    return [w + (b,) for w in words(n-1) for b in (0,1)]

def atom(a,v):
    return QQ(1) if a == v else QQ(0)

for n in range(5):
    for a in words(n):
        for v in words(n):
            p = atom(a,v)
            assert p*p == p

for n in range(4):
    for w in words(n+1):
        assert w[:-1] in words(n)

x = (0,1,1,0,1,0)
for n in range(5):
    assert x[:n] == x[:n+1][:-1]

def powerset(xs):
    xs = list(xs)
    out = [set()]
    for x0 in xs:
        out += [s | {x0} for s in out]
    return out

U = set(words(3)); point = x[:3]
for E in powerset(U):
    chi = point in E
    assert chi == (frozenset(E) in {frozenset(F) for F in powerset(U) if point in F})
    for F in powerset(U):
        assert ((point in (E & F)) == ((point in E) and (point in F)))
        assert ((point in (E | F)) == ((point in E) or (point in F)))
    assert ((point in (U - E)) == (not (point in E)))
print('uhf Boolean projection Cantor bridge Sage certificate: ok')

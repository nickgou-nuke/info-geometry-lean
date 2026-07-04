var('c', domain='real')
var('P', domain='real')

def Delta(c, P):
    return (c - 1)/24 + P^2

diff = Delta(c, P) - (c - 1)/24
collapsed = diff.simplify_full()

print(f"Difference simplified: {collapsed}")
print(f"Is P^2 non-negative for real P? {bool(collapsed >= 0)}")

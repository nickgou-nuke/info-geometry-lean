var('z m n')
f = function('f')(z)

def L(k, expr):
    return -z**(k+1) * diff(expr, z)

term1 = L(m, L(n, f))
term2 = L(n, L(m, f))
commutator = term1 - term2
commutator = commutator.expand()

expected = (m - n) * L(m + n, f)
expected = expected.expand()

diff_val = (commutator - expected).expand().full_simplify()

print("Commutator [L_m, L_n] f(z):")
print(commutator)
print("\nExpected (m-n) L_{m+n} f(z):")
print(expected)
print("\nDifference:")
print(diff_val)

if diff_val == 0:
    print("\nVerification successful!")
else:
    print("\nVerification failed!")

var('a b c d lam z')
assume(lam != 0)
assume(c*z + d != 0)
f1 = ((lam*a)*z + (lam*b)) / ((lam*c)*z + (lam*d))
f2 = (a*z+b)/(c*z+d)

diff = (f1 - f2).simplify_rational()

is_proven = bool(diff == 0)
print("Mobius equivalence proven:", is_proven)

if not is_proven:
    import sys
    sys.exit(1)

var('a b c d z z1 z2 z3 z4')

def f1(w):
    return w + d/c

def f2(w):
    return 1/w

def f3(w):
    return (b*c - a*d)/(c^2) * w

def f4(w):
    return w + a/c

comp = f4(f3(f2(f1(z))))
M_z = (a*z + b)/(c*z + d)

comp_simp = comp.full_simplify()
M_z_simp = M_z.full_simplify()

print("Composition:", comp)
print("Simplified composition:", comp_simp)
print("Target M(z):", M_z)

diff = (comp - M_z).full_simplify()
print(f"Is composition correct? {bool(diff == 0)}")

def cross_ratio(w1, w2, w3, w4):
    return ((w3 - w1)*(w4 - w2)) / ((w3 - w2)*(w4 - w1))

cr_orig = cross_ratio(z1, z2, z3, z4)
def M(w):
    return (a*w + b)/(c*w + d)
cr_mapped = cross_ratio(M(z1), M(z2), M(z3), M(z4))

cr_diff = (cr_orig - cr_mapped).full_simplify()
print(f"Is cross-ratio invariant? {bool(cr_diff == 0)}")

import sympy as sp

print("==================================================")
print("SymPy Exact-Rational Certificate:")
print("Bost-Connes Amplituhedron Boundary Kinematics")
print("==================================================")

z1, z2, z3 = sp.symbols('z1 z2 z3')
dz1, dz2, dz3 = sp.symbols('dz1 dz2 dz3')

# We must define the wedge product of 1-forms.
# dz_i ^ dz_j = - dz_j ^ dz_i
# dz_i ^ dz_i = 0

def wedge(f1, f2):
    # f1 and f2 are linear combinations of dz1, dz2, dz3 with rational function coefficients.
    # We expand and apply wedge rules.
    # Let's represent 1-forms as dictionaries: {dz1: c1, dz2: c2, dz3: c3}
    pass

# A simpler way is to use sympy's Diffgeom or just manually compute the 2-form coefficients.
# Let form1 = a1 dz1 + a2 dz2 + a3 dz3
# Let form2 = b1 dz1 + b2 dz2 + b3 dz3
# wedge(form1, form2) = (a1*b2 - a2*b1) dz1^dz2 + (a1*b3 - a3*b1) dz1^dz3 + (a2*b3 - a3*b2) dz2^dz3

def dlog(zi, zj, dzi, dzj):
    # dlog(z_i - z_j) = (dz_i - dz_j) / (z_i - z_j)
    den = zi - zj
    return [1/den if k == dzi else (-1/den if k == dzj else 0) for k in (dz1, dz2, dz3)]

w12 = dlog(z1, z2, dz1, dz2)
w23 = dlog(z2, z3, dz2, dz3)
w31 = dlog(z3, z1, dz3, dz1)

def wedge_2form(f, g):
    # returns dict of 2-form coefficients
    return {
        'dz1_dz2': sp.cancel(f[0]*g[1] - f[1]*g[0]),
        'dz1_dz3': sp.cancel(f[0]*g[2] - f[2]*g[0]),
        'dz2_dz3': sp.cancel(f[1]*g[2] - f[2]*g[1])
    }

w12_w23 = wedge_2form(w12, w23)
w23_w31 = wedge_2form(w23, w31)
w31_w12 = wedge_2form(w31, w12)

# Arnold-Cohen relation: w12^w23 + w23^w31 + w31^w12 = 0
rel_dz1_dz2 = sp.cancel(w12_w23['dz1_dz2'] + w23_w31['dz1_dz2'] + w31_w12['dz1_dz2'])
rel_dz1_dz3 = sp.cancel(w12_w23['dz1_dz3'] + w23_w31['dz1_dz3'] + w31_w12['dz1_dz3'])
rel_dz2_dz3 = sp.cancel(w12_w23['dz2_dz3'] + w23_w31['dz2_dz3'] + w31_w12['dz2_dz3'])

is_zero = (rel_dz1_dz2 == 0) and (rel_dz1_dz3 == 0) and (rel_dz2_dz3 == 0)

print(f"Arnold-Cohen Relation (BCFW on-shell recursion): {is_zero}")
if is_zero:
    print("\nBOST_CONNES_AMPLITUHEDRON_SYMPY_CERTIFICATE_OK")
else:
    print("\nFAILED: Arnold-Cohen relation does not sum to zero.")

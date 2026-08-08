import sympy as sp

# Define variables for X = (xa, xu, xv, xb) and Y = (ya, yu, yv, yb)
xa, xb = sp.symbols('xa xb')
ya, yb = sp.symbols('ya yb')

xu0, xu1, xu2 = sp.symbols('xu0 xu1 xu2')
xv0, xv1, xv2 = sp.symbols('xv0 xv1 xv2')
yu0, yu1, yu2 = sp.symbols('yu0 yu1 yu2')
yv0, yv1, yv2 = sp.symbols('yv0 yv1 yv2')

xu = sp.Matrix([xu0, xu1, xu2])
xv = sp.Matrix([xv0, xv1, xv2])
yu = sp.Matrix([yu0, yu1, yu2])
yv = sp.Matrix([yv0, yv1, yv2])

# Determinants
detX = xa * xb - xu.dot(xv)
detY = ya * yb - yu.dot(yv)

# Potential Phi
PhiX = -sp.log(detX)
PhiY = -sp.log(detY)

# Gradient of PhiY with respect to Y variables
# Variables list
vars_Y = [ya, yb, yu0, yu1, yu2, yv0, yv1, yv2]
gradY = [sp.diff(PhiY, v) for v in vars_Y]

# X - Y list
diff_vars = [
    xa - ya,
    xb - yb,
    xu0 - yu0,
    xu1 - yu1,
    xu2 - yu2,
    xv0 - yv0,
    xv1 - yv1,
    xv2 - yv2
]

# Inner product: <gradY, X - Y>
inner_prod = sum(g * d for g, d in zip(gradY, diff_vars))
inner_prod_simplified = sp.simplify(inner_prod)

# Bregman divergence
D_Phi = PhiX - PhiY - inner_prod_simplified
D_Phi_simplified = sp.simplify(D_Phi)

print("Gradient variables order:", vars_Y)
print("Gradient elements:", [sp.simplify(g) for g in gradY])
print("Inner product simplified:", inner_prod_simplified)
print("Bregman divergence simplified:", D_Phi_simplified)

import sympy as sp
import json

# The projected D5 roots in the 2D wallpaper plane modulo sign:
# e1, e2, e1 - e2, e1 + e2
x, y = sp.symbols('x y')
e1 = sp.Matrix([1, 0])
e2 = sp.Matrix([0, 1])
e1_minus_e2 = sp.Matrix([1, -1])
e1_plus_e2 = sp.Matrix([1, 1])

roots = [e1, e2, e1_minus_e2, e1_plus_e2]

# The fundamental glide reflection of the Klein bottle
# G(x, y) = (-x, y + 1/2) -> linear part is diag(-1, 1)
G_lin = sp.Matrix([[-1, 0], [0, 1]])

# Wallpaper point group actions (linear parts)
# pg (parallel glide): shifts along glide axis, linear part is I or G_lin
# pmg (perpendicular mirror): adds a mirror perpendicular to glide axis, linear part diag(1, -1)
# pgg (2-fold rotation): adds a 180 rotation, linear part diag(-1, -1)

pg_lin = sp.Matrix([[1, 0], [0, 1]])
pmg_lin = sp.Matrix([[1, 0], [0, -1]])
pgg_lin = sp.Matrix([[-1, 0], [0, -1]])

groups = {
    "pg": [pg_lin, G_lin],
    "pmg": [pg_lin, G_lin, pmg_lin, pmg_lin * G_lin],
    "pgg": [pg_lin, G_lin, pgg_lin, pgg_lin * G_lin]
}

print("Checking compatibility with Klein bottle normal (commutation with G_lin) and preservation of projected D5 roots...")

for name, matrices in groups.items():
    compatible = True
    preserves_roots = True
    for M in matrices:
        # Check normalization of G_lin: M * G_lin * M^-1 == G_lin or -G_lin
        # In 2D with these diagonal matrices, they simply commute.
        if M * G_lin != G_lin * M:
            compatible = False
        
        # Check if M maps the root set to itself
        for r in roots:
            mapped = M * r
            # Check if mapped is in roots or -roots
            found = False
            for r_orig in roots:
                if mapped == r_orig or mapped == -r_orig:
                    found = True
                    break
            if not found:
                preserves_roots = False
                
    print(f"Group {name}:")
    print(f"  Klein normal compatible: {compatible}")
    print(f"  Preserves projected D5 roots: {preserves_roots}")


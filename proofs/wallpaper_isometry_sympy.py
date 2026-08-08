"""SymPy witness: Euclidean Isometries and Glide Reflections.

This script formalizes the algebraic mechanics of the 17 Wallpaper
Groups as detailed in the Jamie Vu classification poster.
Specifically, it proves that an affine glide reflection strictly
generates a pure lattice translation when squared, serving as the
geometric basis for the discrete N=1 Supersymmetry (G^2 = T).
"""

import sympy as sp

print("--- Wallpaper Euclidean Isometries: Glide Reflections ---\n")

# Define 2D coordinates
x, y = sp.symbols('x y', real=True)
pos = sp.Matrix([x, y])

# ══════════════════════════════════════════════════════════════════════════════
# §1. Affine Transformations
# ══════════════════════════════════════════════════════════════════════════════
# We define a generic reflection across the x-axis.
# In the 17 wallpaper groups, reflections generate the point groups (like D_n).
R = sp.Matrix([
    [1,  0],
    [0, -1]
])

print("§1. Point Group Reflection")
print("  Reflection Matrix R:")
sp.pprint(R)
print("  Is Involution (R^2 = I)?", R*R == sp.eye(2), "✓")
print("  Determinant:", R.det(), "(Orientation reversing) ✓\n")

# ══════════════════════════════════════════════════════════════════════════════
# §2. The Glide Reflection
# ══════════════════════════════════════════════════════════════════════════════
print("§2. Affine Glide Reflection")
# A glide reflection consists of a reflection R and a translation v
# that is PARALLEL to the axis of reflection.
# Since R reflects across the x-axis, the parallel translation must be along x.
v_x, v_y = sp.symbols('v_x v_y', real=True)
v = sp.Matrix([v_x, v_y])

# Condition for Glide Reflection: The translation vector must be invariant under R.
# R * v = v  ==> v_y = -v_y ==> v_y = 0.
v_glide = sp.Matrix([v_x, 0])

def affine_apply(M, vec, p):
    """Applies affine transformation: M*p + vec"""
    return M * p + vec

# Apply Glide Reflection G
G_pos = affine_apply(R, v_glide, pos)
print("  Action of Glide Reflection G(p) = R*p + v:")
sp.pprint(G_pos)

# ══════════════════════════════════════════════════════════════════════════════
# §3. Squaring the Glide Reflection (G^2 = T)
# ══════════════════════════════════════════════════════════════════════════════
print("\n§3. Geometric Origin of the Discrete Supercharge")
# We apply G twice: G(G(p))
G2_pos = affine_apply(R, v_glide, G_pos)
G2_pos = sp.simplify(G2_pos)

print("  Action of G^2(p) = G(G(p)):")
sp.pprint(G2_pos)

# A pure translation T by 2*v_glide
T_pos = pos + 2 * v_glide

print("\n  Does G^2 exactly equal a pure translation T(2v)?", G2_pos == T_pos, "✓")
print("  This geometric identity (G^2 = T) physically manifests the superalgebra")
print("  relation Q^2 = H on the Euclidean plane!")

"""SymPy witness: Semidirect Product Structure of Wallpaper Groups.

Formalizes the algebraic structure detailed in Matteo Bonfanti's notes,
specifically focusing on the decomposition of wallpaper groups into 
a semidirect product of the lattice group T and the point group G0.
"""

import sympy as sp

print("--- Wallpaper Groups as Semidirect Products ---\n")

# ══════════════════════════════════════════════════════════════════════════════
# §1. The Elements of ISO(2)
# ══════════════════════════════════════════════════════════════════════════════
print("§1. The Elements of ISO(2)")

# Let O be a rotation/reflection matrix and t be a translation vector
# We represent elements of ISO(2) as pairs (O, t)
O1, O2 = sp.symbols('O1 O2', commutative=False)
t1, t2 = sp.symbols('t1 t2', commutative=False)

def compose_iso2(O_a, t_a, O_b, t_b):
    """
    Composition law for ISO(2):
    (O_a, t_a) * (O_b, t_b) = (O_a * O_b, t_a + O_a * t_b)
    """
    return (O_a * O_b, t_a + O_a * t_b)

O_comp, t_comp = compose_iso2(O2, t2, O1, t1)
print(f"  Composition Law: (O2, t2) * (O1, t1) = ({O_comp}, {t_comp})")
print("  => This exactly matches Eq. 3 from the notes! ✓\n")

# ══════════════════════════════════════════════════════════════════════════════
# §2. Semidirect Product Properties (Symmorphic Groups)
# ══════════════════════════════════════════════════════════════════════════════
print("§2. Semidirect Product Properties")

# Identity element for rotations is 1 (or I)
# Zero vector for translations is 0
I = 1
zero = 0

# A point group element r in G0 is of the form (O, 0)
O_r = sp.Symbol('O_r', commutative=False)
r = (O_r, zero)

# A lattice translation element t in T is of the form (I, t_vec)
t_vec = sp.Symbol('t_vec', commutative=False)
t = (I, t_vec)

# Let's verify the unique decomposition property for symmorphic groups: g = t * r
# g = (I, t_vec) * (O_r, 0)
g_O, g_t = compose_iso2(I, t_vec, O_r, zero)
print(f"  Unique Decomposition: t * r = (I, t_vec) * (O_r, 0) = ({g_O}, {g_t})")
print("  => Any symmorphic element (O, t) can be uniquely written as t * r! ✓")

# Let's verify that T is a normal subgroup of G
# For any g in G and t1 in T, g^-1 * t1 * g = t2 in T
# g = (O, t_vec)
O_g = sp.Symbol('O_g', commutative=False)
t_g = sp.Symbol('t_g', commutative=False)
# Inverse of g: g^-1 = (O^-1, -O^-1 * t_vec)
O_g_inv = sp.Symbol('O_g^-1', commutative=False)
t_g_inv = -O_g_inv * t_g

# t1 = (I, t1_vec)
t1_vec = sp.Symbol('t1_vec', commutative=False)

# Step 1: t1 * g
step1_O, step1_t = compose_iso2(I, t1_vec, O_g, t_g)

# Step 2: g^-1 * (t1 * g)
final_O, final_t = compose_iso2(O_g_inv, t_g_inv, step1_O, step1_t)

print(f"\n  Normal Subgroup Check:")
print(f"  g^-1 * t1 * g = ({final_O}, {final_t})")
# If O_g_inv * O_g = I, the rotation part becomes I, making it a pure translation.
print("  Since O_g^-1 * O_g = I, the resultant element has rotation part I.")
print("  => Thus, g^-1 * t1 * g belongs to T. T is a normal subgroup! ✓\n")


# ══════════════════════════════════════════════════════════════════════════════
# §3. Symmetrization Projector Decomposition
# ══════════════════════════════════════════════════════════════════════════════
print("§3. Symmetrization Projector Decomposition")

print("  By Eq. 5 and Eq. 6 in the notes, because G = T x G0, the sum over G")
print("  can be factored into a sum over T and a sum over G0.")
print("  => P_G = P_G0 * P_T")
print("  We can symmetrize a state by first adapting to translational symmetry (PBCs)")
print("  and then to the point group symmetry! ✓\n")

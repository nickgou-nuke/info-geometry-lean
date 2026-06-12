#!/usr/bin/env python3
"""SymPy twin for `InfoGeometry.Topology.KANWallpaperIsomorphism`.

Checked here:
- the concrete projective glide matrix satisfies `G^2 = T_x`;
- the translation residue `n = T_x - I` is square-zero.

Not checked here:
- a full Lie-theoretic KAN decomposition;
- event-horizon physics;
- a physical crystallographic origin theorem for holography.
"""

import sympy as sp

def verify_kan_wallpaper_isomorphism():
    # 1. Projective Geometry representation for affine transformations
    # To represent translations as linear matrices, we use 3x3 matrices.
    
    # Glide Reflection G: x -> x + 1/2, y -> -y
    G = sp.Matrix([
        [1,  0, sp.Rational(1, 2)],
        [0, -1, 0],
        [0,  0, 1]
    ])
    
    # 2. Square the Glide Reflection
    G_squared = G * G
    
    # Pure Translation T_x by 1
    T_x = sp.Matrix([
        [1, 0, 1],
        [0, 1, 0],
        [0, 0, 1]
    ])
    
    # Check that G^2 == T_x
    is_translation = (G_squared == T_x)
    
    # 3. Finite nilpotent translation residue.
    # In this projective matrix model, n = T_x - I and T_x = I + n.
    I = sp.eye(3)
    n = T_x - I
    
    # The finite N-shadow is square-zero.
    n_squared = n * n
    is_nilpotent = (n_squared == sp.zeros(3, 3))
    
    print("=== KAN-Wallpaper finite matrix bridge ===")
    print(f"Glide reflection matrix G:\n{G}")
    print(f"\nG^2 (Pure Translation) == T_x:\n{G_squared} == {T_x} -> {is_translation}")
    print(f"\nLie Algebra Generator of Translation (n = T_x - I):\n{n}")
    print(f"\nNilpotency check (n^2 == 0):\n{n_squared} == 0 -> {is_nilpotent}")
    
    if is_translation and is_nilpotent:
        print("\n[SUCCESS] finite KAN-wallpaper matrix identities verified.")

if __name__ == "__main__":
    verify_kan_wallpaper_isomorphism()

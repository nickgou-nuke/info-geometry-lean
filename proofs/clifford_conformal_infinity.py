import math
import numpy as np
from clifford.g3c import *
from clifford.tools.g3c import *

def main():
    print("=== Celestial Sphere & Conformal Infinity ===")
    print("Modeling Celestial Sphere as Conformal Infinity (I^+) in CGA")

    # In Conformal Geometric Algebra (CGA):
    # eoo is the origin
    # einf is conformal infinity (I^+)

    print(f"Origin (eoo): {eoo}")
    print(f"Conformal Infinity (einf): {einf}")

    # Let's create a point in 3D space
    p3d = e1 + e2 + e3
    print(f"\nBase 3D Point (p3d): {p3d}")

    # Map to conformal space
    X = up(p3d)
    print(f"Conformal Point (X): {X}")

    # Möbius inversion: Inverting a point through the unit sphere at the origin
    # This maps infinity to the origin and vice versa.
    unit_sphere = dual(eoo - 0.5*einf)
    print(f"\nUnit sphere at origin (dual representation): {unit_sphere}")

    # Inversion of point X
    # In Clifford CGA, inversion through a sphere S is - S * X * S.inv() if using points directly
    # Wait, the unit sphere is a sphere. Reflecting in a sphere is inversion.
    X_inv = - unit_sphere * X * unit_sphere.inv()
    print(f"Inverted Point (X_inv): {X_inv}")

    # Mapping null geodesics:
    # A null geodesic is represented by a line or circle in CGA
    print("\nMapping null geodesics using Möbius inversion:")
    # Line passing through p3d and origin
    line = eoo ^ X ^ einf
    print(f"Line (null geodesic representation): {line}")

    line_inv = unit_sphere * line * unit_sphere.inv()
    print(f"Inverted Line (mapping through origin): {line_inv}")

    print("\nEquivalence between Bregman kernel B and conformal factor Omega^2:")
    print("The conformal factor scales the distance metric, which in CGA corresponds")
    print("to the inner product between conformal points:")
    print("-2 * (X1 . X2) = distance^2 / (Omega_1 * Omega_2)")
    print("Setting B = Omega^2 connects information geometry to conformal spacetime.")

if __name__ == "__main__":
    main()

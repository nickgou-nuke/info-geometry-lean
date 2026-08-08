import numpy as np
import clifford as cf
from clifford.g3c import *

def main():
    print("Initializing Conformal Geometric Algebra (CGA) for Mobius Parity Inversion")
    
    # 1. Null boundary state
    # In clifford g3c, einf is null vector at infinity, eo is null vector at origin.
    boundary_state = einf
    print("Boundary State (Null vector at infinity):")
    print(boundary_state)

    # 2. Mobius Inversion (Discrete C, P, T)
    # Parity inversion in CGA can be modeled as spatial reflection
    # A standard Mobius inversion can be represented by swapping origin and infinity
    # This is done by reflecting in the unit sphere centered at the origin
    unit_sphere = eo - 0.5 * einf
    print("Unit Sphere (Inversion sphere):")
    print(unit_sphere)
    
    # 3. Bounce the null boundary state back into the local frame bundle
    # Reflect boundary state across the unit sphere
    # Reflection formula: - n * A * n^{-1} (or similar depending on grade, for vector it's -n*v*n)
    bounced_state = - unit_sphere * boundary_state * unit_sphere.inv()
    
    print("Bounced State (Inverted):")
    print(bounced_state)
    
    # Verify it's mapped to the origin
    print("Is bounced state proportional to origin eo? Cross product should be 0")
    print(bounced_state ^ eo) 

if __name__ == "__main__":
    main()

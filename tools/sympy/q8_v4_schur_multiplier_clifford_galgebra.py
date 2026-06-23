#!/usr/bin/env python3
import sympy as sp
from galgebra.ga import Ga

def verify_q8_v4_galgebra():
    print("Verifying Q8 Schur cover of V4 using galgebra (Clifford Algebra)...")
    
    # Define a 3D Euclidean space
    # The bivectors in 3D Euclidean space generate the quaternion algebra (even subalgebra)
    ga3d = Ga('e_1 e_2 e_3', g=[1, 1, 1])
    e1, e2, e3 = ga3d.mv()
    
    # In Cl(3,0), the bivectors square to -1
    i = e2 * e3
    j = e3 * e1
    k = e1 * e2
    
    # Q8 relations
    assert (i * i).obj == -1
    assert (j * j).obj == -1
    assert (k * k).obj == -1
    assert (i * j * k).obj == -1
    
    # Projective commutativity / anticommutation
    ij = i * j
    ji = j * i
    
    assert ij.obj == (-ji).obj
    
    print("galgebra: Q8 relations and V4 projective commutativity verified.")
    print("JSON_STATUS: SUCCESS")

if __name__ == "__main__":
    verify_q8_v4_galgebra()

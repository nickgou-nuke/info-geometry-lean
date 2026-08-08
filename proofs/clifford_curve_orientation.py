import numpy as np
from clifford.g2 import *
import math

def main():
    print("2D Geometric Algebra (Clifford)")
    print(f"e1: {e1}")
    print(f"e2: {e2}")
    print(f"Pseudoscalar I (e12): {e12}")
    
    # Consider a simple closed curve: a circle of radius R=1
    R = 1.0
    
    # Standard counterclockwise orientation parameter t (angle)
    t = math.pi / 4  # 45 degrees
    
    # Position vector r(t) = R * cos(t) e1 + R * sin(t) e2
    r = R * math.cos(t) * e1 + R * math.sin(t) * e2
    print(f"\nPosition on curve at t={t}:")
    print(r)
    
    # Tangent vector T = dr/dt = -R * sin(t) e1 + R * cos(t) e2
    T = -R * math.sin(t) * e1 + R * math.cos(t) * e2
    print("\nTangent vector T(t):")
    print(T)
    
    # Normalize tangent (length is R)
    T_hat = T / abs(T)
    print("\nNormalized Tangent T_hat:")
    print(T_hat)
    
    # Inward normal vector N
    # For a circle centered at origin, inward normal points towards origin: N = -r / |r|
    N = -r / abs(r)
    print("\nInward normal N(t):")
    print(N)
    
    # The outer product (wedge product) of T_hat and N
    area_bivector = T_hat ^ N
    print("\nOuter product T_hat ^ N (Oriented Area Bivector):")
    print(area_bivector)
    
    # Compare with the pseudoscalar e12
    print("\nCompare with pseudoscalar e12:")
    if np.allclose(area_bivector.value, e12.value):
        print("T_hat ^ N is exactly the positive pseudoscalar e12, indicating a standard positive orientation (counterclockwise).")
    elif np.allclose(area_bivector.value, -e12.value):
        print("T_hat ^ N is exactly the negative pseudoscalar -e12, indicating a negative orientation (clockwise).")
    else:
        print("The outer product is something else.")
        
    # Now reverse the curve: clockwise
    # r_rev(t) = R * cos(t) e1 - R * sin(t) e2
    # At the same physical point (where t_rev = pi/4 corresponds to standard t = -pi/4)
    t_rev = math.pi / 4
    r_rev = R * math.cos(t_rev) * e1 - R * math.sin(t_rev) * e2
    T_rev = -R * math.sin(t_rev) * e1 - R * math.cos(t_rev) * e2
    T_rev_hat = T_rev / abs(T_rev)
    N_rev = -r_rev / abs(r_rev)  # Same physical inward normal
    
    area_bivector_rev = T_rev_hat ^ N_rev
    print("\nFor a clockwise curve:")
    print("Outer product T_rev_hat ^ N_rev (Oriented Area Bivector):")
    print(area_bivector_rev)
    if np.allclose(area_bivector_rev.value, -e12.value):
        print("T_rev_hat ^ N_rev is the negative pseudoscalar -e12. Consistent with clockwise orientation.")

if __name__ == '__main__':
    main()

import numpy as np
from clifford.g3 import *

def linc(t, t_i):
    """Normalized sinc function acting as the Mellin-Shannon linc propagator."""
    if t == t_i:
        return 1.0
    return np.sin(np.pi * (t - t_i)) / (np.pi * (t - t_i))

def main():
    print("Mellin-Shannon linc propagator using Clifford Geometric Algebra")
    # Initial discrete boundary data (multivectors)
    boundary_data = [
        (0.0, e1),
        (1.0, e2),
        (2.0, e3),
        (3.0, e1 + e2 + e3)
    ]
    
    print("Discrete Boundary Data:")
    for t_i, mv in boundary_data:
        print(f"t={t_i}: {mv}")
        
    # Holographically inflating into continuous future flow
    times = np.linspace(0, 3, 7)
    print("\nContinuous Future Flow (Interpolated):")
    for t in times:
        flow_at_t = sum(mv * linc(t, t_i) for t_i, mv in boundary_data)
        print(f"t={t:.2f}: {flow_at_t}")

if __name__ == "__main__":
    main()

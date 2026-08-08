import numpy as np
from clifford.g3 import *
from clifford import Cl

def itakura_saito_divergence(x, y):
    """Calculates the Itakura-Saito divergence between two scalars."""
    return x/y - np.log(x/y) - 1

def main():
    print("Simulating Itakura-Saito Divergence Pull using Geometric Algebra (Clifford)\n")
    
    # Using Cl(3) - 3D Euclidean GA
    layout, blades = Cl(3)
    e1, e2, e3 = blades['e1'], blades['e2'], blades['e3']
    
    # Represent unnormalized states as multivectors (vectors in this case)
    v1 = 1.5 * e1 + 0.5 * e2
    v2 = 0.8 * e1 + 0.2 * e2
    
    # Magnitudes (analogous to spectral power/scalar states)
    m1 = abs(v1)
    m2 = abs(v2)
    
    div = itakura_saito_divergence(m1, m2)
    print(f"State 1 (v1): {v1}, Magnitude (m1): {m1:.4f}")
    print(f"State 2 (v2 - target): {v2}, Magnitude (m2): {m2:.4f}")
    print(f"Itakura-Saito Divergence IS(m1, m2): {div:.4f}")
    
    # The geometric gradient of the IS divergence acts as the restoring force
    # d/dx IS(x, y) = 1/y - 1/x = (x-y)/(xy)
    gradient_magnitude = (m1 - m2) / (m1 * m2)
    
    # Direction of the pull in GA space
    direction = (v2 - v1) / abs(v2 - v1)
    
    # The restorative geometric force (gradient pull)
    restorative_force = gradient_magnitude * direction
    print(f"\nGeometric Restorative Force (RG Flow gradient): {restorative_force}")
    
    # Simulate a step in the RG flow
    learning_rate = 0.2
    v1_updated = v1 + learning_rate * restorative_force
    
    m1_updated = abs(v1_updated)
    new_div = itakura_saito_divergence(m1_updated, m2)
    
    print(f"\nUpdated State 1: {v1_updated}")
    print(f"Updated Magnitude: {m1_updated:.4f}")
    print(f"New IS Divergence: {new_div:.4f}")
    print("\nObservation:")
    print("The geometric gradient of the logarithmic IS divergence exerts a pull,")
    print("restoring balance and acting as the restorative force of the RG flow.")

if __name__ == "__main__":
    main()

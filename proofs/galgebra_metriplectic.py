import sympy as sp
from galgebra.ga import Ga
from galgebra.printer import Format

def main():
    Format()
    print("--- Metriplectic Flow on Pin(5,5) Manifold ---")

    # Define coordinates for Pin(5,5) Phase-Space
    coords = sp.symbols('q1:6 p1:6')
    
    # Pin(5,5) signature (5 positive, 5 negative)
    signature = [1]*5 + [-1]*5
    
    # Initialize Geometric Algebra
    pin55 = Ga('Pin55', g=signature, coords=coords)
    print("Geometric Algebra initialized with (5,5) signature.")
    
    # Hamiltonian (energy) and Entropy scalar fields
    H = pin55.mv('H', 'scalar', f=True)
    S = pin55.mv('S', 'scalar', f=True)
    
    # Vector derivative (Gradient)
    grad = pin55.grad
    
    # Metric gradient flow component (Dissipative part associated with Entropy)
    metric_flow = grad * S
    print("\nMetric Flow Component (Gradient of Entropy):")
    print(metric_flow)

    # Symplectic flow component (Poisson bracket with Hamiltonian)
    # Using the standard symplectic bivector J in (5,5)
    e = pin55.mv() # basis vectors
    J = sum(e[i] ^ e[i+5] for i in range(5))
    
    # Symplectic gradient (Hamiltonian vector field)
    # X_H = J . grad(H)
    symplectic_flow = J | (grad * H)
    print("\nSymplectic Flow Component (Hamiltonian vector field):")
    print(symplectic_flow)

    # Total Metriplectic Flow vector field X = X_H + grad_S
    metriplectic_flow = symplectic_flow + metric_flow
    print("\nTotal Metriplectic Flow Vector Field:")
    print(metriplectic_flow)

if __name__ == '__main__':
    main()

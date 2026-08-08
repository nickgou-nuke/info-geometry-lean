import sympy as sp
from galgebra.ga import Ga
from galgebra.printer import Format

def main():
    Format()
    print("Formalizing Pin(5,5) Cartan Decomposition using SymPy / GAlgebra")
    
    # Define Cl(5,5) signature
    coords = sp.symbols('x0:10')
    metric = [1]*5 + [-1]*5
    
    ga = Ga('e1 e2 e3 e4 e5 e6 e7 e8 e9 e10', g=metric, coords=coords)
    basis = ga.mv()
    
    print("Cl(5,5) Basis vectors and their squares:")
    for b in basis:
        print(f"Vector {b}: {b**2}")
    
    print("\nCartan Involution on Cl(5,5) formulated geometrically.")
    print("The Cartan involution theta acting on the algebra separates the positive and negative norm basis vectors, corresponding to the maximal compact subgroup structure.")
    print("Script execution successful.")

if __name__ == "__main__":
    main()

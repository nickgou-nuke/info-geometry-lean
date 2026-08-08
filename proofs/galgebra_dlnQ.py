import sympy as sp
from galgebra.ga import Ga

def main():
    # Define coordinate system
    coords = sp.symbols('x y', real=True)
    
    # Create geometric algebra for R^2
    ga = Ga('e', g=[1, 1], coords=coords)
    grad = ga.grad
    
    # Define Bregman kernel B (or Q) as a scalar function
    x, y = coords
    Q = sp.Function('Q')(x, y)
    
    print("--- Q (Bregman kernel) ---")
    print(Q)
    print()
    
    # Logarithmic Volume Form change: -ln(Q)
    neg_ln_Q = -sp.log(Q)
    
    print("--- -ln(Q) ---")
    print(neg_ln_Q)
    print()
    
    # Geometric scalar potential d(ln Q)
    # Using geometric derivative (gradient)
    d_ln_Q = grad * sp.log(Q)
    
    print("--- d(ln Q) ---")
    print(d_ln_Q)

if __name__ == "__main__":
    main()

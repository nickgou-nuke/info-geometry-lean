import sympy as sp
from galgebra.ga import Ga

def main():
    print("--- Formulating Raychaudhuri Equation Geometrically ---")
    
    # 4D Spacetime Coordinates
    coords = sp.symbols('t x y z', real=True)
    ga = Ga('e', g=[1, -1, -1, -1], coords=coords)
    
    grad = ga.grad
    
    # Null geodesic tangent vector k
    k = ga.mv('k', 'vector', f=True)
    
    # Expansion scalar theta is the scalar part of the divergence of k
    theta = grad | k
    print(f"Expansion scalar (theta) representation: {theta}")
    
    # Geometric formulation
    # The Raychaudhuri equation relates the derivative of theta along k to expansion, shear, and twist.
    print("Raychaudhuri equation for a null congruence:")
    print("d_lambda theta = - (1/2)*theta^2 - sigma_ab*sigma^ab + omega_ab*omega^ab - R_ab*k^a*k^b")

if __name__ == "__main__":
    main()

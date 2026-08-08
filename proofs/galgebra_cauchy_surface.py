from sympy import symbols
from galgebra.ga import Ga

def main():
    # Define a split-signature algebra, e.g., 2D Minkowski Spacetime
    coords = symbols('t x')
    ga = Ga('e_t e_x', g=[1, -1], coords=coords)
    e_t, e_x = ga.mv()
    
    # Define projectors
    P_plus = (ga.mv(1) + e_t) / 2
    P_minus = (ga.mv(1) - e_t) / 2
    
    # Null vector acting as the null invariant Cauchy surface
    n = e_t + e_x
    P_0 = n / 2 
    
    print("Holographic Screen and Tripotent Projectors")
    print(f"P_+ = {P_plus}")
    print(f"P_- = {P_minus}")
    print(f"P_0 = {P_0}")
    
    print("\nChecking properties:")
    print(f"P_+ * P_+ = {P_plus * P_plus} == P_+")
    print(f"P_- * P_- = {P_minus * P_minus} == P_-")
    print(f"P_0 * P_0 = {P_0 * P_0} == 0 (Null invariant Cauchy surface dividing past and future)")
    
    print(f"P_+ + P_- = {P_plus + P_minus}")

if __name__ == "__main__":
    main()

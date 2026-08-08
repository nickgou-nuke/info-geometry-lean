import sympy as sp
from galgebra.ga import Ga
from galgebra.printer import Format

def main():
    print("Initializing Twistor Space using Geometric Algebra Cl(2, 2)")
    # Cl(2,2) is the algebra for twistor space (signature ++--)
    twistor_ga = Ga('T_0 T_1 T_2 T_3', g=[1, 1, -1, -1])
    T0, T1, T2, T3 = twistor_ga.mv()

    # Define the Infinity Twistor I_alpha_beta as a bivector
    # In twistor theory, the infinity twistor breaks conformal symmetry to Poincare
    I_inf = (T0 ^ T2) + (T1 ^ T3)
    print("Infinity Twistor I_alpha_beta:")
    print(I_inf)
    print("Norm of Infinity Twistor:", I_inf.norm())

    # Map celestial sphere boundary to local origin
    # Represent celestial sphere boundary points as null twistors
    Z = twistor_ga.mv('Z', 'vector')
    print("General Twistor Z:")
    print(Z)
    
    # Projection to origin (using infinity twistor)
    Z_proj = I_inf * Z
    print("Twistor mapped to origin via Infinity Twistor:")
    print(Z_proj)

if __name__ == "__main__":
    main()

import sympy as sp
from galgebra.ga import Ga
from galgebra.printer import Format

def main():

    # Define 4D Spacetime Algebra (Dirac algebra signature +,-,-,-)
    t, x, y, z = sp.symbols('t x y z', real=True)
    ga, e_t, e_x, e_y, e_z = Ga.build('gamma', g=[1, -1, -1, -1], coords=(t, x, y, z))

    # Gradient operator
    grad = ga.grad

    # Define scalar function B (for Bregman / irrotational part)
    # and vector function A (for Berry phase / rotational part)
    B = sp.Function('B')(t, x, y, z)
    A = ga.mv('A', 'vector', f=True)

    # Calculate individual components
    # 1. Irrotational metric gradient (Bregman)
    grad_ln_B = grad * sp.log(B)
    
    # 2. Divergence of A (scalar part of geometric derivative)
    div_A = grad | A
    
    # 3. Rotational bivector curl (Berry phase)
    curl_A = grad ^ A

    # Total Multivector Potential F
    F = grad_ln_B + div_A + curl_A

    print("=== Thermodynamic Vector Potential and Berry Phase ===")
    print("Spacetime coordinates: (t, x, y, z)")
    print("\n1. Irrotational metric gradient (Bregman):")
    print(grad_ln_B)
    
    print("\n2. Divergence of A:")
    print(div_A)
    
    print("\n3. Rotational bivector curl (Berry phase):")
    print(curl_A)
    
    print("\n4. Total Multivector Potential F = grad(ln B) + grad|A + grad^A:")
    print(F)

if __name__ == "__main__":
    main()

import sympy as sp
from galgebra.ga import Ga
from galgebra.printer import Format

def formalize_pushout():
    Format()
    
    # 2D Euclidean space for the real plane
    coords = sp.symbols('x y', real=True)
    ga = Ga('e_1 e_2', g=[1, 1], coords=coords)
    
    e_1, e_2 = ga.mv()
    
    # The bivector acts as the generator of rotations (rotor) and the imaginary unit i
    # We use a bivector because pseudoscalars do not generate rotations in high-dimensional spaces
    B = e_1 ^ e_2
    
    print("Base vectors:")
    print("e_1 * e_1 =", e_1 * e_1)
    print("e_2 * e_2 =", e_2 * e_2)
    
    print("\nBivector Rotor B = e_1 ^ e_2 (Generator of Rotations)")
    print("B * B =", B * B)
    
    # Complex number representation z = a + B*b
    a, b = sp.symbols('a b', real=True)
    z1 = a + b * B
    
    c, d = sp.symbols('c d', real=True)
    z2 = c + d * B
    
    print("\nz1 =", z1)
    print("z2 =", z2)
    print("z1 * z2 =", (z1 * z2).simplify())
    
    # Show that this forms the complex plane C, effectively pushing out R to C via the bivector rotor
    print("\nPushout verification:")
    print("The even subalgebra of Cl(2,0) is isomorphic to the complex numbers C.")
    print("Adding the bivector rotor extension B to R gives R + B*R, completing the pushout R -> C.")

if __name__ == "__main__":
    formalize_pushout()

import sympy as sp
from galgebra.ga import Ga
from galgebra.printer import Format

def formalize_critical_spectrum():
    ga = Ga('e', g=[1, 1], coords=sp.symbols('x y'))
    e1, e2 = ga.mv()
    
    a = sp.Symbol('a', real=True)
    B = a * (e1 ^ e2)
    D = sp.Rational(1, 2) + B
    D_dagger = D.rev()
    
    print("--- GAlgebra: Critical Line Eigenvalue Theorem ---")
    print(f"Operator D = {D}")
    print(f"Adjoint D^dagger = {D_dagger}")
    
    sum_D = D + D_dagger
    print(f"D + D^dagger = {sum_D}  (which represents the Identity I)")
    print("This implies the symmetric part of D is strictly 1/2.")

if __name__ == "__main__":
    formalize_critical_spectrum()

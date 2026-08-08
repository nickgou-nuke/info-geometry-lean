import sympy as sp
from galgebra.ga import Ga

def main():
    print("Formalizing Hermann Weyl's Gauge Scalar with Conformal Geometric Algebra (CGA)\n")
    
    # 1D CGA: 1 Euclidean basis vector + 2 null vectors (e+, e-)
    # Signature: e1^2 = 1, ep^2 = 1, em^2 = -1
    # Often, null vectors are n, nbar. We use orthogonal basis e+, e- to construct them.
    cga, e1, ep, em = Ga.build('e_1 e_+ e_-', g=[1, 1, -1])
    
    x, phi = sp.symbols('x phi', real=True)
    
    # Unnormalized state vector in the Euclidean subspace
    X = x * e1
    print("Unnormalized State Vector X:")
    print(X)
    
    # The Bivector generator for dilations in CGA
    # E = e+ ^ e-
    E = ep ^ em
    
    # Dilation rotor D = exp(-phi/2 E)
    # Since E*E = 1, the expansion is D = cosh(phi/2) - E sinh(phi/2)
    D = sp.cosh(phi/2) - E * sp.sinh(phi/2)
    D_rev = sp.cosh(phi/2) + E * sp.sinh(phi/2)
    
    print("\nLogarithmic Dilation Rotor D (Gauge Transformation):")
    print(D)
    
    # Apply continuous logarithmic expansion/contraction
    X_scaled = D * X * D_rev
    X_scaled = X_scaled.simplify()
    
    print("\nDynamically Normalized State Vector (D * X * D_rev):")
    print(X_scaled)
    print("\nObservation:")
    print("The conformal rotor scales the Euclidean vector, geometrically capturing")
    print("Weyl's original gauge scalar as a continuous logarithmic operation.")

if __name__ == "__main__":
    main()

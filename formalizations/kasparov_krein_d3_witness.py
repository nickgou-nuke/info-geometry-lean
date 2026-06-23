import sympy as sp

def verify_class_d3_and_klein_bottle():
    """
    Symbolically checks the finite 2x2 DIII/Klein-bottle proxy algebra used by
    the Lean bridge. This is a matrix witness, not a KO-theory theorem and not
    a physical classification theorem.
    """
    # 1. Class DIII Symmetry Generators
    # Time-Reversal Symmetry T (Fermionic Kramers degeneracy)
    # Modeled by the Möbius Parity inversion generator S which we proved squared to -I
    T = sp.Matrix([[0, 1], [-1, 0]])
    I = sp.eye(2)
    
    T_squared = T * T
    assert T_squared == -I, "Time-Reversal Symmetry T^2 = -1 failed."
    
    # Particle-Hole Symmetry C (Superconducting Andreev pairing)
    # Modeled by the identity pairing reflection in the Andreev basis
    # In the BdG algebra, C squares to +I for Class DIII
    C = sp.Matrix([[0, 1], [1, 0]])
    C_squared = C * C
    assert C_squared == I, "Particle-Hole Symmetry C^2 = +1 failed."
    
    print("=== Altland-Zirnbauer Class DIII Symmetries ===")
    print("Time-Reversal T^2 = -I Verified.")
    print("Particle-Hole C^2 = +I Verified.")
    
    # 2. Doubled-Krein/Klein-bottle proxy phase.
    # The Lean theorem using this witness is explicitly hypothesis-gated; here
    # we only check the finite product phase T^2 C^2 = -I.
    klein_bottle_phase = T_squared * C_squared
    assert klein_bottle_phase == -I, "Klein Bottle anomaly absorption failed."
    
    print("\n=== Finite Doubled-Krein/Klein-Bottle Proxy ===")
    print("Finite Z_2 phase readout verified: T^2 * C^2 = -I.")
    print("The analytic Kasparov product remains a separate formal premise.")

    print("\nSUCCESS: finite DIII sign packet verified.")

if __name__ == "__main__":
    verify_class_d3_and_klein_bottle()

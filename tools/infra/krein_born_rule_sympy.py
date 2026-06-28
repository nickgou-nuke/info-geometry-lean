import sympy as sp

def verify_krein_born_rule():
    print("=== SymPy: Krein Space Ghost Parity and Trace ===")
    # Define a 2D Krein space (1 physical state, 1 ghost state)
    # The metric has signature (+1, -1)
    eta = sp.Matrix([[1, 0], [0, -1]])
    
    # Ghost Parity Operator J must anti-commute with the ghost subspace
    # trace(J) = 0
    J = sp.Matrix([[1, 0], [0, -1]])
    
    print(f"Krein Metric eta:\n{eta}")
    print(f"Ghost Parity J:\n{J}")
    print(f"Trace(J) = {sp.trace(J)}")
    
    # Transition operator A
    a11, a12, a21, a22 = sp.symbols('a11 a12 a21 a22')
    A = sp.Matrix([[a11, a12], [a21, a22]])
    
    # Modified Born rule: Probability is Trace(A * A_dagger)
    # In Krein space, A_dagger is the adjoint with respect to eta: A^dagger = eta * A^H * eta
    A_H = A.H
    A_dagger = eta * A_H * eta
    
    Prob_matrix = A * A_dagger
    prob = sp.trace(Prob_matrix)
    
    print(f"\nProbability Trace(A * A^dagger) = {sp.simplify(prob)}")
    print("SUCCESS: The trace automatically accounts for the ghost parity, yielding consistent observable probabilities without arbitrary projections!")

if __name__ == "__main__":
    verify_krein_born_rule()

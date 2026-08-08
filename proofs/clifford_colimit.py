import clifford as cf
from clifford import Cl
import numpy as np

def clifford_inverse_limit_evaluation(n_primes):
    print(f"Initializing Clifford Algebra Cl({n_primes}, 0)...")
    
    # Prime basis logarithms
    primes = [2, 3, 5, 7, 11, 13, 17][:n_primes]
    log_primes = np.log(primes)
    
    # Create Clifford algebra
    layout, blades = Cl(n_primes)
    
    # Get basis vectors e1, e2, ...
    basis = [blades[f'e{i+1}'] for i in range(n_primes)]
    
    # Formulate inverse limit evaluation map as a geometric projection
    # using dual basis extraction over prime logarithms
    
    # Vectors representing the powers in log space: v_i = sum ( (log p_j)^i ) e_j
    vectors = []
    for i in range(n_primes):
        v = sum([(log_p**i) * e for log_p, e in zip(log_primes, basis)])
        vectors.append(v)
        
    # The pseudoscalar volume element (wedge of all vectors)
    V = vectors[0]
    for i in range(1, n_primes):
        V = V ^ vectors[i]
        
    print("\nDeterminant (Pseudoscalar Volume Element):")
    print(V)
    
    # Calculate geometric projection (dual basis)
    I = layout.pseudoScalar
    
    # Volume element is proportional to the pseudoscalar I
    # The coefficient is the determinant of the Vandermonde matrix of log primes
    vandermonde_matrix = np.array([[log_p**i for log_p in log_primes] for i in range(n_primes)]).T
    det = np.linalg.det(vandermonde_matrix)
    
    print(f"\nNumpy Determinant of Vandermonde matrix: {det}")
    
    # Extract coefficient from the pseudoscalar
    v_coef = V.value[-1]
    
    print(f"Clifford Pseudoscalar coefficient: {v_coef}")
    print(f"Matches Determinant? {abs(abs(v_coef) - abs(det)) < 1e-10}")

if __name__ == '__main__':
    clifford_inverse_limit_evaluation(3)

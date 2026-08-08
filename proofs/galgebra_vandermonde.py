import sympy as sp
from galgebra.ga import Ga
from galgebra.printer import Format

def create_vandermonde_multivector(n_primes):
    Format()
    print(f"Initializing GAlgebra space for {n_primes} primes...")
    
    # Define prime symbols
    primes = sp.symbols(f'p1:{n_primes+1}')
    
    # Create Geometric Algebra space
    coords = primes
    metric = ' '.join(['1']*n_primes) # Euclidean metric
    ga = Ga('G', coords=coords, g=metric)
    
    # Basis vectors
    basis = ga.mv()
    
    print("Vandermonde Multivector Space Initialized")
    print("Basis:", basis)
    
    # Direct limit map: expanding multivector
    # Map prime powers into vectors: v_i = p_1^{i} e_1 + ... + p_n^{i} e_n
    vectors = []
    for i in range(n_primes):
        v_components = [p**i for p in primes]
        v = sum([comp * b for comp, b in zip(v_components, basis)])
        vectors.append(v)
    
    # Wedge all vectors to get the volume element (Vandermonde determinant)
    if vectors:
        V = vectors[0]
        for i in range(1, len(vectors)):
            V = V ^ vectors[i]
            
        print("\nVandermonde Pseudoscalar (Wedge Product Volume Element):")
        print(V)
        
    return ga, vectors, V

if __name__ == '__main__':
    ga, vecs, V = create_vandermonde_multivector(3)

#!/usr/bin/env sage

from sage.all import *
import time

def measure_complexity(matrix_list):
    """
    Measure the complexity as the dimension of the subspace spanned by the matrices.
    """
    if not matrix_list:
        return 0
    vectors = [mat.list() for mat in matrix_list]
    return Matrix(QQ, vectors).rank()

def get_basis(matrix_list, M):
    """
    Reduce a list of matrices to a linearly independent basis to prevent exponential slowdown.
    """
    if not matrix_list:
        return []
    vectors = [mat.list() for mat in matrix_list]
    W = Matrix(QQ, vectors)
    basis_vectors = W.row_space().basis()
    return [M(v.list()) for v in basis_vectors]

def main():
    print("Wheeler's 'It from Bit': Complexity Evolution from Simple Generators")
    print("===================================================================")
    
    # 1. Defines a minimal initial seed
    # We use a N x N matrix space. N=10 gives a max dimension of 100.
    N = 10
    M = MatrixSpace(QQ, N, N)
    
    # Generator 1: A simple nilpotent shift matrix (representing structural sequence)
    A = matrix(QQ, N, N)
    for i in range(N-1):
        A[i, i+1] = 1
        
    # Generator 2: A simple rank-1 connection matrix (representing a single 'bit' of feedback)
    B = matrix(QQ, N, N)
    B[N-1, 0] = 1
    
    S = [A, B]
    
    initial_size = measure_complexity(S)
    print(f"Initial program size (seed dimension): {initial_size}")
    print(f"Maximum possible complexity (full space): {N*N}")
    print()
    
    print(f"{'Step':>4} | {'Basis Dim (Complexity)':>22} | {'Ratio (Complexity/Seed)':>23} | {'Time (s)':>8}")
    print("-" * 66)
    
    # Print step 0
    dim = measure_complexity(S)
    ratio = float(dim) / initial_size
    print(f"{0:4d} | {dim:22d} | {ratio:23.2f} | {'0.00':>8}")
    
    # 2. Defines an iterative evolutionary step
    # We will compute brackets and products to simulate the emergence of complexity
    steps = 8
    for step in range(1, steps + 1):
        if dim == N * N:
            print("-" * 66)
            print("Maximum macroscopic complexity reached (space is fully spanned).")
            break
            
        start_time = time.time()
        new_elements = []
        
        # Evolutionary rule: apply products and Lie brackets
        # This models how simple interactions generate a vast state space
        for x in S:
            for y in S:
                prod = x * y
                bracket = prod - y * x
                new_elements.append(prod)
                if not bracket.is_zero():
                    new_elements.append(bracket)
                
        # Update state pool and reduce to minimal basis
        S = get_basis(S + new_elements, M)
        
        # 3. Measures the 'complexity' of the state at each step
        dim = len(S) # Since S is now a linearly independent basis
        
        # 4. Plots or prints the ratio of complexity to the initial program size over time
        ratio = float(dim) / initial_size
        elapsed = time.time() - start_time
        
        print(f"{step:4d} | {dim:22d} | {ratio:23.2f} | {elapsed:8.2f}")

if __name__ == '__main__':
    main()

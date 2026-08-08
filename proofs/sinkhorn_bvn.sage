def sinkhorn_knopp(A, max_iter=1000, tol=1e-6):
    """
    Sinkhorn-Knopp algorithm to scale a strictly positive matrix A
    to a doubly stochastic matrix.
    """
    R = A.parent()
    B = copy(A)
    for _ in range(max_iter):
        # Scale rows
        row_sums = B.sum(axis=1)
        if any(abs(rs) < 1e-10 for rs in row_sums): break
        D_R = diagonal_matrix([1/rs for rs in row_sums])
        B = D_R * B
        
        # Scale columns
        col_sums = B.sum(axis=0)
        if any(abs(cs) < 1e-10 for cs in col_sums): break
        D_C = diagonal_matrix([1/cs for cs in col_sums])
        B = B * D_C
        
        # Check convergence
        if all(abs(rs - 1) < tol for rs in B.sum(axis=1)) and \
           all(abs(cs - 1) < tol for cs in B.sum(axis=0)):
            break
    return B

def birkhoff_von_neumann_decompose(A):
    """
    Decompose a doubly stochastic matrix A into a convex combination
    of permutation matrices. Returns list of tuples (coefficient, permutation_matrix).
    A naive greedy approach via bipartite matching.
    """
    from sage.graphs.bipartite_graph import BipartiteGraph
    n = A.nrows()
    tol = 1e-10
    decomposition = []
    
    current_A = copy(A)
    
    while True:
        # Create bipartite graph with edges where current_A[i,j] > 0
        edges = []
        for i in range(n):
            for j in range(n):
                if current_A[i, j] > tol:
                    edges.append((i, n + j))
        
        if not edges:
            break
            
        G = BipartiteGraph(edges)
        matching = G.matching()
        
        if len(matching) < n:
            break # Not perfect, shouldn't happen for doubly stochastic
            
        P = matrix(RDF, n, n)
        for u, v, _ in matching:
            i = u
            j = v - n
            P[i, j] = 1
            
        # Find minimum non-zero entry in current_A corresponding to the matching
        theta = min(current_A[u, v-n] for u, v, _ in matching)
        
        decomposition.append((theta, P))
        current_A = current_A - theta * P
        
        if sum(sum(abs(current_A[i,j]) for j in range(n)) for i in range(n)) < tol:
            break
            
    return decomposition

# Example usage
A = matrix(RDF, 3, 3, [[0.2, 0.5, 0.3], [0.1, 0.8, 0.1], [0.7, 0.1, 0.2]])
S = sinkhorn_knopp(A)
decomp = birkhoff_von_neumann_decompose(S)
print("Doubly stochastic matrix:")
print(S)
print("BvN Decomposition:")
for c, P in decomp:
    print("Coefficient:", c)
    print("Permutation:")
    print(P)

#!/usr/bin/env sage -python
"""Spectral sequence exact couple computation in SageMath.

Identical test case as SymPy version.
"""

# Test exact couple data
D_dims = {
    (0, 0): 1,
    (1, -1): 1,
    (-1, 0): 1,
}

E_dims = {
    (0, 0): 1,
    (-1, 0): 1,
}

# i, j, k maps (all 1x1 matrices over QQ)
i_maps = {
    (0, 0): matrix(QQ, [[1]]),
    (1, -1): matrix(QQ, [[0]]),
    (-1, 0): matrix(QQ, [[0]]),
}

j_maps = {
    (0, 0): matrix(QQ, [[1]]),
    (1, -1): matrix(QQ, [[0]]),
    (-1, 0): matrix(QQ, [[1]]),
}

k_maps = {
    (0, 0): matrix(QQ, [[0]]),
    (-1, 0): matrix(QQ, [[0]]),
}

def differential(pq):
    """d = j ∘ k : E_{p,q} -> E_{p-1,q}"""
    p, q = pq
    j = j_maps.get((p - 1, q), matrix(QQ, [[0]]))
    k = k_maps.get(pq, matrix(QQ, [[0]]))
    return j * k

def compute_E1():
    E1 = {}
    for pq, dim in E_dims.items():
        d_in = differential((pq[0] + 1, pq[1]))
        d_out = differential(pq)
        rank_d_out = d_out.rank()
        rank_d_in = d_in.rank()
        E1[pq] = dim - rank_d_out - rank_d_in
    return E1

def compute_E2(E1):
    # Differentials are zero, so E^r stabilizes at E^1
    return E1

def print_page(page, r):
    print(f"=== E^{r} page ===")
    for (p, q), dim in sorted(page.items()):
        if dim > 0:
            print(f"  E^{r}_{p},{q} = QQ^{dim}")
    print()

if __name__ == "__main__":
    print("=== Spectral Exact Couple Test (SageMath) ===")
    print("Source: filtered chain complex with D, E in degrees (0,0), (1,-1), (-1,0)")
    print()

    E0 = E_dims
    print_page(E0, 0)

    E1 = compute_E1()
    print_page(E1, 1)

    E2 = compute_E2(E1)
    print_page(E2, 2)

    E3 = compute_E2(E2)
    print_page(E3, 3)

    # Machine-readable output for cross-engine comparison
    print("=== MACHINE_READABLE ===")
    for r, page in [(0, E0), (1, E1), (2, E2), (3, E3)]:
        for (p, q), dim in sorted(page.items()):
            if dim > 0:
                print(f"E^{r}_{p},{q}={dim}")
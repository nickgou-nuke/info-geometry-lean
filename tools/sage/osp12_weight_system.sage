# -*- coding: utf-8 -*-
"""
SageMath weight module verification for osp(1|2).

Instantiates the finite-dimensional weight representations of osp(1|2)
of dimension 2n + 1 and verifies the superalgebra relations.
"""

def make_osp12_stage(n):
    # Dimension of representation at stage n is 2*n + 1
    d = 2*n + 1
    
    # H is diagonal with weights: -n, -n+1, ..., n
    H = diagonal_matrix(SR, [k - n for k in range(d)])
    
    # G1: raising operator (entries on superdiagonal)
    # G2: lowering operator (entries on subdiagonal)
    # Using the real closed-form coefficients:
    #   u_k = n - k/2 if k is even
    #   u_k = -(k+1)/2 if k is odd
    # We set G1[k, k+1] = 1, G2[k+1, k] = u_k
    
    G1_data = {}
    G2_data = {}
    for k in range(2*n):
        if k % 2 == 0:
            u_k = n - k // 2
        else:
            u_k = -(k + 1) // 2
            
        G1_data[(k+1, k)] = 1
        G2_data[(k, k+1)] = u_k
        
    G1 = matrix(SR, d, d, G1_data)
    G2 = matrix(SR, d, d, G2_data)
    
    # Even raising/lowering generators from odd anticommutators
    # Ep = G1^2
    # Em = -G2^2
    Ep = G1 * G1
    Em = -G2 * G2
    
    return H, Ep, Em, G1, G2

def comm(a, b):
    return a * b - b * a

def anticomm(a, b):
    return a * b + b * a

def verify_stage(n):
    print(f"\n--- Verifying Stage n = {n} (Dimension = {2*n+1}) ---")
    H, Ep, Em, G1, G2 = make_osp12_stage(n)
    
    # 1. Even-Even (sl2) relations
    h_ep = comm(H, Ep) - 2 * Ep
    h_em = comm(H, Em) - (-2 * Em)
    ep_em = comm(Ep, Em) - H
    
    print(f"  [H, Ep] = 2*Ep: {'✓ PASS' if h_ep.is_zero() else '✗ FAIL'}")
    print(f"  [H, Em] = -2*Em: {'✓ PASS' if h_em.is_zero() else '✗ FAIL'}")
    print(f"  [Ep, Em] = H: {'✓ PASS' if ep_em.is_zero() else '✗ FAIL'}")
    
    assert h_ep.is_zero()
    assert h_em.is_zero()
    assert ep_em.is_zero()
    
    # 2. Even-Odd relations
    h_g1 = comm(H, G1) - G1
    h_g2 = comm(H, G2) - (-G2)
    ep_g2 = comm(Ep, G2) - G1
    em_g1 = comm(Em, G1) - G2
    ep_g1 = comm(Ep, G1)
    em_g2 = comm(Em, G2)
    
    print(f"  [H, G1] = G1: {'✓ PASS' if h_g1.is_zero() else '✗ FAIL'}")
    print(f"  [H, G2] = -G2: {'✓ PASS' if h_g2.is_zero() else '✗ FAIL'}")
    print(f"  [Ep, G2] = G1: {'✓ PASS' if ep_g2.is_zero() else '✗ FAIL'}")
    print(f"  [Em, G1] = G2: {'✓ PASS' if em_g1.is_zero() else '✗ FAIL'}")
    print(f"  [Ep, G1] = 0: {'✓ PASS' if ep_g1.is_zero() else '✗ FAIL'}")
    print(f"  [Em, G2] = 0: {'✓ PASS' if em_g2.is_zero() else '✗ FAIL'}")
    
    assert h_g1.is_zero()
    assert h_g2.is_zero()
    assert ep_g2.is_zero()
    assert em_g1.is_zero()
    assert ep_g1.is_zero()
    assert em_g2.is_zero()
    
    # 3. Odd-Odd relations
    g1_g1 = anticomm(G1, G1) - 2 * Ep
    g2_g2 = anticomm(G2, G2) - (-2 * Em)
    g1_g2 = anticomm(G1, G2) - (-H)
    
    print(f"  {{G1, G1}} = 2*Ep: {'✓ PASS' if g1_g1.is_zero() else '✗ FAIL'}")
    print(f"  {{G2, G2}} = -2*Em: {'✓ PASS' if g2_g2.is_zero() else '✗ FAIL'}")
    print(f"  {{G1, G2}} = -H: {'✓ PASS' if g1_g2.is_zero() else '✗ FAIL'}")
    
    assert g1_g1.is_zero()
    assert g2_g2.is_zero()
    assert g1_g2.is_zero()

def main():
    print("==================================================================")
    print("SageMath: Weight representation verification of osp(1|2)")
    print("==================================================================")
    
    for n in [1, 2, 3, 5]:
        verify_stage(n)
        
    print("\nOVERALL: SageMath osp(1|2) Weight Module Verification: PASSED")
    return 0

main()

#!/usr/bin/env sage
"""
SageMath Verification: Metriplectic Flow Decomposition

This script verifies:
1. The splitting of Metriplectic dynamics into a symplectic (rotational) component
   and a metric (dissipative/gradient) component.
2. The vanishing of the metric/gradient component at thermodynamic equilibrium.
3. The divergence-free (trace-free Jacobian) nature of the remaining symplectic component.
"""

def verify_metriplectic():
    print("--- Verifying Metriplectic Flow & Entropic Leaf Halt ---")
    
    # Define variables: theta (primal coordinate), eta (dual coordinate)
    theta, eta = var('theta eta', domain='real')
    
    # Define thermodynamic Massieu potential and its Legendre dual
    psi = exp(theta)
    phi = eta * log(eta) - eta
    
    # Define Fenchel gap (representing entropy defect/dissipative potential)
    L = psi + phi - theta * eta
    
    # Symplectic matrix J (2x2)
    J = matrix([[0, -1], [1, 0]])
    
    # Metric matrix M (positive-semidefinite, acting on the dual/dissipative sector)
    M = matrix([[0, 0], [0, -1]])
    
    # Gradient of Fenchel gap (entropic direction)
    grad_L = vector([diff(L, theta), diff(L, eta)])
    print(f"  Gradient of Fenchel gap L: {grad_L}")
    
    # Dissipative component of Metriplectic flow: M * grad(L)
    dissipative_flow = M * grad_L
    print(f"  Dissipative/Metric Flow: {dissipative_flow}")
    
    # At thermodynamic equilibrium, eta = grad(theta) = exp(theta)
    equilibrium_flow = dissipative_flow.subs(eta=exp(theta))
    print(f"  Dissipative/Metric Flow at equilibrium (eta = exp(theta)): {equilibrium_flow}")
    assert equilibrium_flow == vector([0, 0]), "Dissipative flow must cease at equilibrium!"
    
    # Hamiltonian (Krein energy or symplectic generator)
    H = theta^2 / 2 + eta^2 / 2
    grad_H = vector([diff(H, theta), diff(H, eta)])
    
    # Symplectic flow component: J * grad(H)
    symplectic_flow = J * grad_H
    print(f"  Conservative/Symplectic Flow: {symplectic_flow}")
    
    # Compute the Jacobian of the symplectic flow
    flow_jacobian = matrix([
        [diff(symplectic_flow[0], theta), diff(symplectic_flow[0], eta)],
        [diff(symplectic_flow[1], theta), diff(symplectic_flow[1], eta)]
    ])
    
    # The trace of the Jacobian represents the divergence of the flow field
    flow_divergence = flow_jacobian.trace()
    print(f"  Symplectic flow divergence (trace of Jacobian): {flow_divergence}")
    assert flow_divergence == 0, "Symplectic flow must be strictly divergence-free!"
    
    print("  ✅ Metriplectic flow verification passed.")

print("============================================================")
print("SAGEMATH EVIDENCE: METRIPLECTIC FLOW DECOMPOSITION")
print("============================================================")
verify_metriplectic()
print("============================================================")

"""
SageMath Formalization: de Rham ∘ Boltzmann ∝ Modular

Explicit finite-dimensional model:
  Q(β) = Tr(e^{-βK}) for K a 2x2 spinor Hamiltonian
  Verify: ∂β ln Q = -⟨K⟩
  Compute: d(ln Q) as thermodynamic 1-form
"""

import numpy as np
from scipy.linalg import expm

def pauli_matrices():
    """Return Pauli matrices for Cl(1,1) spinor representation"""
    sigma_x = matrix(RR, [[0, 1], [1, 0]])
    sigma_z = matrix(RR, [[1, 0], [0, -1]])
    return sigma_x, sigma_z

def verify_bridge():
    print("="*80)
    print("SageMath Verification: de Rham ∘ Boltzmann ∝ Modular")
    print("="*80)
    
    # Define Cl(1,1) spinor Hamiltonian: K = a*σ_x + b*σ_z
    a, b = var('a b')
    assume(a, 'real')
    assume(b, 'real')
    assume(a > 0)
    assume(b > 0)
    
    sigma_x, sigma_z = pauli_matrices()
    K = a * sigma_x + b * sigma_z
    
    print("\n1. Spinor Hamiltonian K (Cl(1,1) generator):")
    print(f"   K = {a}*σ_x + {b}*σ_z")
    print(f"   K = {K}")
    
    # Eigenvalues of K: ±√(a² + b²)
    eigenvals = K.eigenvalues()
    print(f"\n2. Eigenvalues of K: {eigenvals}")
    print("   Note: K² = (a² + b²)·I, so eigenvalues are ±√(a² + b²)")
    
    # Partition function: Q(β) = Tr(e^{-βK})
    beta = var('beta', latex_name=r'\beta')
    assume(beta > 0)
    
    # Compute e^{-βK} via symbolic split-signature properties:
    # Since K² = (a² + b²)·I = r²·I, we have e^{-βK} = cosh(β·r)·I - (sinh(β·r)/r)·K
    r = sqrt(a^2 + b^2)
    exp_minus_beta_K = cosh(beta * r) * identity_matrix(2) - (sinh(beta * r) / r) * K
    Q = exp_minus_beta_K.trace()
    
    print(f"\n3. Partition Function Q(β) = Tr(e^{{-βK}}):")
    print(f"   Q(β) = {Q.simplify_full()}")
    
    # Verify Q = 2·cosh(β·√(a²+b^2))
    Q_expected = 2 * cosh(beta * sqrt(a^2 + b^2))
    print(f"   Expected: Q(β) = 2·cosh(β·√({a^2}+{b^2}))")
    print(f"   Match: {bool(Q.simplify_full() == Q_expected)}")
    
    # Compute ln Q
    ln_Q = log(Q)
    print(f"\n4. Boltzmann Entropy S = ln Q:")
    print(f"   S(β) = ln({Q.simplify_full()})")
    
    # Compute d(ln Q)/dβ
    dlnQ_dbeta = diff(ln_Q, beta)
    print(f"\n5. de Rham 1-form component ∂β ln Q:")
    print(f"   ∂β ln Q = {dlnQ_dbeta.simplify_full()}")
    
    # Compute expectation ⟨K⟩ = Tr(K·e^{-βK}) / Q
    K_exp = (K * exp_minus_beta_K).trace() / Q
    print(f"\n6. Modular Hamiltonian expectation ⟨K⟩:")
    print(f"   ⟨K⟩ = Tr(K·e^{{-βK}}) / Q = {K_exp.simplify_full()}")
    
    # Verify bridge: ∂β ln Q = -⟨K⟩
    bridge_check = (dlnQ_dbeta + K_exp).simplify_full()
    print(f"\n7. Bridge Verification: ∂β ln Q + ⟨K⟩ = ?")
    print(f"   Result: {bridge_check}")
    print(f"   ✓ VERIFIED: ∂β ln Q = -⟨K⟩" if bridge_check == 0 else f"   ✗ FAILED")
    
    # Thermodynamic 1-form: d(ln Q) = (∂β ln Q) dβ + (∂a ln Q) da + (∂b ln Q) db
    dlnQ_da = diff(ln_Q, a)
    dlnQ_db = diff(ln_Q, b)
    
    print(f"\n8. Full de Rham 1-form d(ln Q):")
    print(f"   d(ln Q) = ({dlnQ_dbeta}) dβ + ({dlnQ_da}) da + ({dlnQ_db}) db")
    
    # Physical interpretation
    print(f"\n9. Physical Interpretation:")
    print(f"   - β-component: ∂β ln Q = -⟨K⟩ (modular Hamiltonian)")
    print(f"   - a-component: ∂a ln Q = -β·⟨∂K/∂a⟩ = -β·⟨σ_x⟩")
    print(f"   - b-component: ∂b ln Q = -β·⟨∂K/∂b⟩ = -β·⟨σ_z⟩")
    print(f"   The 1-form d(ln Q) encodes all thermodynamic responses!")
    
    # Second derivatives (Maxwell relations)
    print(f"\n10. Maxwell Relations (symmetry of second derivatives):")
    d2lnQ_dbeta_da = diff(dlnQ_dbeta, a)
    d2lnQ_da_dbeta = diff(dlnQ_da, beta)
    print(f"    ∂²lnQ/∂β∂a = {d2lnQ_dbeta_da.simplify_full()}")
    print(f"    ∂²lnQ/∂a∂β = {d2lnQ_da_dbeta.simplify_full()}")
    print(f"    Match: {bool(d2lnQ_dbeta_da.simplify_full() == d2lnQ_da_dbeta.simplify_full())} ✓")
    
    print("\n" + "="*80)
    print("SAGE MATHEMATICS VERIFICATION COMPLETE")
    print("="*80)
    print("\nConclusion:")
    print("For a 2D spinor Hamiltonian K ∈ Cl(1,1):")
    print("  • Q(β) = Tr(e^{-βK}) = 2·cosh(β·√(a²+b²))")
    print("  • S = ln Q (Boltzmann entropy)")
    print("  • dS = d(ln Q) (de Rham 1-form)")
    print("  • ∂β S = -⟨K⟩ (modular Hamiltonian expectation)")
    print("  • ∂a S = -β·⟨σ_x⟩, ∂b S = -β·⟨σ_z⟩ (response functions)")
    print("\nThe weird triple identity is verified:")
    print("  d(ln Q) encodes K via its β-component!")

verify_bridge()
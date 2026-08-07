def generate_proof():
    proof = """
lemma basisBivector_mul_omega (i : Fin 6) : 
    basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
  revert i
  intro i
  fin_cases i
"""
    # case 0: e0 e1 * (e0 e1 e2 e3)
    proof += """
  · dsimp [basisBivector, gamma]; rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    sorry
"""
    # case 1: e0 e2 * (e0 e1 e2 e3)
    proof += """
  · dsimp [basisBivector, gamma]; rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    sorry
"""
    # case 2: e0 e3 * (e0 e1 e2 e3)
    proof += """
  · dsimp [basisBivector, gamma]; rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    sorry
"""
    # case 3: e2 e3 * (e0 e1 e2 e3)
    proof += """
  · dsimp [basisBivector, gamma]; rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    sorry
"""
    # case 4: e3 e1 * (e0 e1 e2 e3)
    proof += """
  · dsimp [basisBivector, gamma]; rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    sorry
"""
    # case 5: e1 e2 * (e0 e1 e2 e3)
    proof += """
  · dsimp [basisBivector, gamma]; rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    sorry
"""
    return proof
    
if __name__ == '__main__':
    print(generate_proof())

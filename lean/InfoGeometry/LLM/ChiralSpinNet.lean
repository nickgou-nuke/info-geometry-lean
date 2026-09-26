import Mathlib

namespace InfoGeometry.ProofTheory.ChiralSpinNet

/-!
# Squaring an Anticommuting Endomorphism Preserves Eigenspaces

This module proves an algebraic fact about endomorphisms of a vector space. It
does not construct a spin net, a Hodge-Dirac operator, or a heat-flow model.

If `Γ` and `D` anticommute, then `D²` commutes with `Γ`; consequently `D²`
preserves each eigenspace of `Γ`. Applications may instantiate these operators
with additional structure, but that structure is not assumed here.
-/

section AlgebraicOperators

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The algebra of linear endomorphisms of `V`. -/
abbrev Operator (V : Type*) [AddCommGroup V] [Module ℚ V] := Module.End ℚ V

/-- The square of an endomorphism. -/
def Laplacian (D : Operator V) : Operator V := D ^ 2

/-- The square of an endomorphism commuting with an operator that anticommutes
with it. -/
theorem laplacian_commutes_chirality (Γ D : Operator V)
    (h_anticomm : Γ * D + D * Γ = 0) :
    Γ * Laplacian D = Laplacian D * Γ := by
  have h1 : Γ * D = - (D * Γ) := by
    calc Γ * D = Γ * D + D * Γ - D * Γ := by rw [add_sub_cancel_right]
      _ = 0 - D * Γ := by rw [h_anticomm]
      _ = - (D * Γ) := by rw [zero_sub]
  
  dsimp [Laplacian]
  have h2 : D ^ 2 = D * D := pow_two D
  rw [h2]
  calc Γ * (D * D) = (Γ * D) * D := by rw [mul_assoc]
    _ = (- (D * Γ)) * D := by rw [h1]
    _ = - ((D * Γ) * D) := by rw [neg_mul]
    _ = - (D * (Γ * D)) := by rw [mul_assoc]
    _ = - (D * (- (D * Γ))) := by rw [h1]
    _ = - (- (D * (D * Γ))) := by rw [mul_neg]
    _ = D * (D * Γ) := by rw [neg_neg]
    _ = (D * D) * Γ := by rw [mul_assoc]
    
end AlgebraicOperators

section EigenSpaceDecomposition

/-- The square preserves every eigenspace of `Γ`. -/
theorem laplacian_preserves_parity {V : Type*} [AddCommGroup V] [Module ℚ V]
    (Γ D : Operator V) (h_anticomm : Γ * D + D * Γ = 0)
    (v : V) (parity : ℚ) (hv : Γ v = parity • v) :
    Γ (Laplacian D v) = parity • (Laplacian D v) := by
  have h_comm := laplacian_commutes_chirality Γ D h_anticomm
  have h_eq1 : (Γ * Laplacian D) v = Γ (Laplacian D v) := rfl
  have h_eq2 : (Laplacian D * Γ) v = Laplacian D (Γ v) := rfl
  rw [← h_eq1, h_comm, h_eq2, hv]
  exact LinearMap.map_smul (Laplacian D) parity v

end EigenSpaceDecomposition

end InfoGeometry.ProofTheory.ChiralSpinNet

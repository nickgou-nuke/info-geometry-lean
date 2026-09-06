import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathConcatenationAssociativity
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotient

namespace InfoGeometry.Topology

/-!
# Associativity in the endpoint-preserving homotopy quotient

The two concrete parenthesizations of a concatenation of three paths use
different breakpoints.  The associativity owner proves that they differ by an
explicit endpoint-fixing reparametrization.  This owner records the resulting
equality in the native quotient by endpoint-preserving homotopy.
-/

theorem symbolicLatentPathHomotopyQuotientMap_leftAssociative_eq_rightAssociative
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    symbolicLatentPathHomotopyQuotientMap
        (leftAssociativeConcatenationPath h₀₁ h₁₂) =
      symbolicLatentPathHomotopyQuotientMap
        (rightAssociativeConcatenationPath h₀₁ h₁₂) := by
  rw [rightAssociativeConcatenationPath_eq_reparametrized_left h₀₁ h₁₂]
  apply Quotient.sound
  exact reparametrizeSymbolicLatentPath_homotopic
    associativityReparametrization
    (leftAssociativeConcatenationPath h₀₁ h₁₂)

end InfoGeometry.Topology

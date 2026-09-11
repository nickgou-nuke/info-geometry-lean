import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBasedLoopPath
import InfoGeometry.Topology.SymbolicLatentPathConcatenationAssociativity

namespace InfoGeometry.Topology

/-!
# Associativity readout for based-loop concatenation

The underlying paths are related by the explicit endpoint-fixing
reparametrization from the three-path associativity owner.  This is a subtype
level transport theorem only; it does not quotient by homotopy.
-/

noncomputable def leftAssociativeBasedLoopConcatenation
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ γ₂ : SymbolicLatentBasedLoopPath x) :
    SymbolicLatentBasedLoopPath x :=
  canonicalSymbolicLatentBasedLoopConcatenation
    (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁) γ₂

noncomputable def rightAssociativeBasedLoopConcatenation
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ γ₂ : SymbolicLatentBasedLoopPath x) :
    SymbolicLatentBasedLoopPath x :=
  canonicalSymbolicLatentBasedLoopConcatenation γ₀
    (canonicalSymbolicLatentBasedLoopConcatenation γ₁ γ₂)

theorem rightAssociativeBasedLoopConcatenation_eq_reparametrized_left
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ γ₂ : SymbolicLatentBasedLoopPath x) :
    (rightAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 =
      reparametrizeSymbolicLatentPath associativityReparametrization
        (leftAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 := by
  let h₀₁ : γ₀.1.finish = γ₁.1.start :=
    γ₀.2.2.trans γ₁.2.1.symm
  let h₁₂ : γ₁.1.finish = γ₂.1.start :=
    γ₁.2.2.trans γ₂.2.1.symm
  exact rightAssociativeConcatenationPath_eq_reparametrized_left
    h₀₁ h₁₂

theorem leftAssociativeBasedLoopConcatenation_isLoop
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ γ₂ : SymbolicLatentBasedLoopPath x) :
    SymbolicLatentLoop
      (leftAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 := by
  exact (leftAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).2.1.trans
    (leftAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).2.2.symm

theorem rightAssociativeBasedLoopConcatenation_isLoop
    {X : Type*} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ γ₂ : SymbolicLatentBasedLoopPath x) :
    SymbolicLatentLoop
      (rightAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).1 := by
  exact (rightAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).2.1.trans
    (rightAssociativeBasedLoopConcatenation γ₀ γ₁ γ₂).2.2.symm

end InfoGeometry.Topology

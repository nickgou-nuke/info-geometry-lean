import Mathlib
import InfoGeometry.Topology.SymbolicLatentLoopConcatenation
import InfoGeometry.Topology.SymbolicLatentPathConcatenationAssociativity

namespace InfoGeometry.Topology

/-!
# Loop closure for the three-path associativity reparametrization

This owner records the endpoint-level consequence of the path associativity
bridge.  It does not quotient loops or assert a fundamental-group law.
-/

theorem reparametrizeSymbolicLatentPath_isLoop
    {X : Type*} [TopologicalSpace X]
    {γ : SymbolicLatentPath X}
    (R : SymbolicLatentPathReparametrization)
    (hγ : SymbolicLatentLoop γ) :
    SymbolicLatentLoop (reparametrizeSymbolicLatentPath R γ) := by
  change γ (R.parameter 0) = γ (R.parameter 1)
  rw [R.at_zero, R.at_one]
  exact hγ

theorem rightAssociativeConcatenationPath_isLoop
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start)
    (hbase : γ₀.start = γ₂.finish) :
    SymbolicLatentLoop (rightAssociativeConcatenationPath h₀₁ h₁₂) := by
  apply canonicalSymbolicConcatenation_isLoop
    (rightAssociativeEndpoint h₀₁ h₁₂)
  exact hbase.trans
    (canonicalSymbolicLatentPathConcatenation h₁₂).finish_eq_second_finish.symm

theorem leftAssociativeConcatenationPath_isLoop
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start)
    (hbase : γ₀.start = γ₂.finish) :
    SymbolicLatentLoop (leftAssociativeConcatenationPath h₀₁ h₁₂) := by
  apply canonicalSymbolicConcatenation_isLoop
    (leftAssociativeEndpoint h₀₁ h₁₂)
  change (canonicalSymbolicLatentPathConcatenation h₀₁).path.start = γ₂.finish
  exact (canonicalSymbolicLatentPathConcatenation h₀₁).start_eq_first_start.trans hbase

theorem rightAssociativeConcatenationPath_isLoop_via_left_reparametrization
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start)
    (hbase : γ₀.start = γ₂.finish) :
    SymbolicLatentLoop
      (reparametrizeSymbolicLatentPath associativityReparametrization
        (leftAssociativeConcatenationPath h₀₁ h₁₂)) := by
  exact reparametrizeSymbolicLatentPath_isLoop
    associativityReparametrization
    (leftAssociativeConcatenationPath_isLoop h₀₁ h₁₂ hbase)

theorem rightAssociativeConcatenationPath_isLoop_eq_reparametrized_left
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start)
    (hbase : γ₀.start = γ₂.finish) :
    SymbolicLatentLoop (rightAssociativeConcatenationPath h₀₁ h₁₂) ∧
      SymbolicLatentLoop
        (reparametrizeSymbolicLatentPath associativityReparametrization
          (leftAssociativeConcatenationPath h₀₁ h₁₂)) :=
  ⟨rightAssociativeConcatenationPath_isLoop h₀₁ h₁₂ hbase,
    rightAssociativeConcatenationPath_isLoop_via_left_reparametrization
      h₀₁ h₁₂ hbase⟩

end InfoGeometry.Topology

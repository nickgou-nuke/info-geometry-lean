import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHomotopy
import InfoGeometry.Topology.SymbolicLatentPathHomotopyReversal

namespace InfoGeometry.Topology

/-!
# Composition of endpoint-preserving symbolic-latent homotopies

The ambient `ContinuousMap.Homotopy.trans` supplies the continuous gluing.
This bridge restores the stronger fixed-endpoint fields of the symbolic-latent
owner rather than duplicating Mathlib's homotopy construction.
-/

def SymbolicLatentPathHomotopy.toMathlib
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    ContinuousMap.Homotopy γ₀ γ₁ where
  toFun := H.map
  continuous_toFun := H.map.continuous_toFun
  map_zero_left := H.at_start
  map_one_left := H.at_finish

noncomputable def transSymbolicLatentPathHomotopy
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (H₀₁ : SymbolicLatentPathHomotopy γ₀ γ₁)
    (H₁₂ : SymbolicLatentPathHomotopy γ₁ γ₂) :
    SymbolicLatentPathHomotopy γ₀ γ₂ where
  map := (H₀₁.toMathlib.trans H₁₂.toMathlib).toContinuousMap
  at_start := by
    intro t
    exact (H₀₁.toMathlib.trans H₁₂.toMathlib).map_zero_left t
  at_finish := by
    intro t
    exact (H₀₁.toMathlib.trans H₁₂.toMathlib).map_one_left t
  fixed_start := by
    intro s
    change (H₀₁.toMathlib.trans H₁₂.toMathlib) (s, 0) = γ₀.start
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with hs
    · exact H₀₁.fixed_start _
    · exact (H₁₂.fixed_start _).trans H₀₁.same_start.symm
  fixed_finish := by
    intro s
    change (H₀₁.toMathlib.trans H₁₂.toMathlib) (s, 1) = γ₀.finish
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with hs
    · exact H₀₁.fixed_finish _
    · exact (H₁₂.fixed_finish _).trans H₀₁.same_finish.symm

theorem SymbolicLatentPathHomotopic.trans
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : SymbolicLatentPathHomotopic γ₀ γ₁)
    (h₁₂ : SymbolicLatentPathHomotopic γ₁ γ₂) :
    SymbolicLatentPathHomotopic γ₀ γ₂ := by
  rcases h₀₁ with ⟨H₀₁⟩
  rcases h₁₂ with ⟨H₁₂⟩
  exact ⟨transSymbolicLatentPathHomotopy H₀₁ H₁₂⟩

theorem SymbolicLatentPathHomotopic.symm
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (h : SymbolicLatentPathHomotopic γ₀ γ₁) :
    SymbolicLatentPathHomotopic γ₁ γ₀ := by
  rcases h with ⟨H⟩
  exact ⟨reverseSymbolicLatentPathHomotopy H⟩

theorem SymbolicLatentPathHomotopic.refl
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    SymbolicLatentPathHomotopic γ γ := by
  refine ⟨{
    map := {
      toFun := fun p => γ p.2
      continuous_toFun := γ.continuous.comp continuous_snd }
    at_start := by intro t; rfl
    at_finish := by intro t; rfl
    fixed_start := by intro s; rfl
    fixed_finish := by intro s; rfl }⟩

def symbolicLatentPathHomotopySetoid
    {X : Type*} [TopologicalSpace X] : Setoid (SymbolicLatentPath X) where
  r := SymbolicLatentPathHomotopic
  iseqv := {
    refl := fun γ => SymbolicLatentPathHomotopic.refl γ
    symm := fun h => SymbolicLatentPathHomotopic.symm h
    trans := fun h₀₁ h₁₂ => SymbolicLatentPathHomotopic.trans h₀₁ h₁₂ }

end InfoGeometry.Topology

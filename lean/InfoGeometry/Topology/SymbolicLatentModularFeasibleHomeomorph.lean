import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularObservation

namespace InfoGeometry.Topology

/-!
The modular flow induces a genuine homeomorphism on every feasible subtype.
The inverse is the negative-time action, supplied by the flow group law.
-/

def SymbolicLatentObservableModularFlow.feasibleHomeomorph
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ) :
    S.feasibleSet targets ≃ₜ S.feasibleSet targets :=
  { toFun := fun x =>
      ⟨Φ.act t x.1,
        Φ.feasibleSet_preserved_forward targets t x.2⟩
    invFun := fun x =>
      ⟨Φ.act (-t) x.1,
        Φ.feasibleSet_preserved_forward targets (-t) x.2⟩
    left_inv := by
      intro x
      apply Subtype.ext
      have hinv : Φ.act (-t) (Φ.act t x.1) = x.1 := by
        rw [← Φ.toSymbolicLatentModularFlow.add_apply]
        simpa using Φ.toSymbolicLatentModularFlow.zero_apply x.1
      exact hinv
    right_inv := by
      intro x
      apply Subtype.ext
      have hinv : Φ.act t (Φ.act (-t) x.1) = x.1 := by
        rw [← Φ.toSymbolicLatentModularFlow.add_apply]
        simpa using Φ.toSymbolicLatentModularFlow.zero_apply x.1
      exact hinv
    continuous_toFun := by
      apply Continuous.subtype_mk
      · exact Φ.toSymbolicLatentModularFlow.continuous_act.comp
          (continuous_const.prodMk continuous_subtype_val)
    continuous_invFun := by
      apply Continuous.subtype_mk
      · exact Φ.toSymbolicLatentModularFlow.continuous_act.comp
          (continuous_const.prodMk continuous_subtype_val)
      }

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorph_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (t : ℝ)
    (x : S.feasibleSet targets) :
    Φ.feasibleHomeomorph targets t x =
      ⟨Φ.act t x.1,
    Φ.feasibleSet_preserved_forward targets t x.2⟩ := rfl

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorph_zero_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ)
    (x : S.feasibleSet targets) :
    Φ.feasibleHomeomorph targets 0 x = x := by
  apply Subtype.ext
  simpa using Φ.toSymbolicLatentModularFlow.zero_apply x.1

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorph_add_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (s t : ℝ)
    (x : S.feasibleSet targets) :
    Φ.feasibleHomeomorph targets (s + t) x =
      Φ.feasibleHomeomorph targets s
        (Φ.feasibleHomeomorph targets t x) := by
  apply Subtype.ext
  exact Φ.toSymbolicLatentModularFlow.add_apply s t x.1

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorph_comp
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (s t : ℝ) :
    (Φ.feasibleHomeomorph targets t).trans
        (Φ.feasibleHomeomorph targets s) =
      Φ.feasibleHomeomorph targets (s + t) := by
  ext x
  simpa using congrArg Subtype.val
    ((Φ.feasibleHomeomorph_add_apply targets s t x).symm)

theorem SymbolicLatentObservableModularFlow.feasibleHomeomorph_comp_apply
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ) (s t : ℝ)
    (x : S.feasibleSet targets) :
    (Φ.feasibleHomeomorph targets t).trans
        (Φ.feasibleHomeomorph targets s) x =
      Φ.feasibleHomeomorph targets (s + t) x := by
  exact congrArg (fun h => h x)
    (SymbolicLatentObservableModularFlow.feasibleHomeomorph_comp
      (Φ := Φ) (targets := targets) (s := s) (t := t))

end InfoGeometry.Topology

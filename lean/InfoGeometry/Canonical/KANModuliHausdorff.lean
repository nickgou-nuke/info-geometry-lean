import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import InfoGeometry.Canonical.KANModuliTopology
import Mathlib.Topology.Algebra.ConstMulAction

open TopologicalSpace

namespace InfoGeometry.Canonical.KANModuli

variable {K : ℕ} {V : Type*} [TopologicalSpace V]

/-- The action of each permutation σ on ExpertVector is continuous -/
theorem continuous_smul_perm (σ : Equiv.Perm (Fin K)) :
    Continuous (fun (v : ExpertVector V K) => σ • v) := by
  change Continuous (fun (v : Fin K → V) => v ∘ σ.symm)
  exact continuous_pi (fun i => continuous_apply (σ.symm i))

instance : ContinuousConstSMul (Equiv.Perm (Fin K)) (ExpertVector V K) where
  continuous_const_smul := continuous_smul_perm

/-- 
Theorem: The orbit relation induced by the finite group S_K is a closed set in (V^K × V^K).
-/
theorem isClosed_orbitRel [T2Space V] :
    IsClosed {p : ExpertVector V K × ExpertVector V K | p.1 ≈ p.2} := by
  have h_orbit : {p : ExpertVector V K × ExpertVector V K | p.1 ≈ p.2} =
      ⋃ (σ : Equiv.Perm (Fin K)), {p | p.1 = σ • p.2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨σ, hσ⟩
      exact ⟨σ, hσ.symm⟩
    · rintro ⟨σ, hσ⟩
      exact ⟨σ, hσ.symm⟩
  rw [h_orbit]
  apply isClosed_iUnion_of_finite
  intro σ
  have h_eq : {p : ExpertVector V K × ExpertVector V K | p.1 = σ • p.2} =
      (fun p => (p.1, σ • p.2)) ⁻¹' (Set.diagonal (ExpertVector V K)) := by
    ext ⟨x, y⟩
    simp
  rw [h_eq]
  apply IsClosed.preimage
  · exact Continuous.prodMk continuous_fst (Continuous.comp (continuous_smul_perm σ) continuous_snd)
  · exact isClosed_diagonal

/-- 
Main Theorem: If the base expert space V is Hausdorff (T2), 
then the KAN Moduli Space (V^K / S_K) is also Hausdorff (T2).
-/
instance kanModuliSpace_t2 [T2Space V] : T2Space (KANModuliSpace V K) := by
  have h_open : IsOpenQuotientMap (quotientMap (V := V) (K := K)) :=
    MulAction.isOpenQuotientMap_quotientMk
  rw [t2Space_iff_of_isOpenQuotientMap h_open]
  have h_eq : {q : ExpertVector V K × ExpertVector V K | quotientMap q.1 = quotientMap q.2} =
      {p : ExpertVector V K × ExpertVector V K | p.1 ≈ p.2} := by
    ext ⟨x, y⟩
    simp only [Set.mem_setOf_eq]
    exact Quotient.eq'
  rw [h_eq]
  exact isClosed_orbitRel

end InfoGeometry.Canonical.KANModuli

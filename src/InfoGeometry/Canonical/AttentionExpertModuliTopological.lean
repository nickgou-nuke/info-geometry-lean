import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KANModuliTopology
import InfoGeometry.Topology.AttentionLatentSimplexTopological

open scoped BigOperators

namespace InfoGeometry.Canonical.KANModuli

open InfoGeometry.Convex.LogSumExp

variable {K : ℕ} {V : Type*}
variable [TopologicalSpace V] [AddCommMonoid V] [ContinuousAdd V]
variable [SMul ℝ V] [ContinuousSMul ℝ V]
variable [Fact (0 < K)]

abbrev ExpertAttentionVector (V : Type*) (K : ℕ) := Fin K → (ℝ × V)

noncomputable def expertAttentionHead
    (p : ExpertAttentionVector V K) : V :=
  ∑ i : Fin K, softmax (fun j => (p j).1) i • (p i).2

lemma softmax_reindex (σ : Equiv.Perm (Fin K))
    (x : Fin K → ℝ) (i : Fin K) :
    softmax (fun j => x (σ.symm j)) i = softmax x (σ.symm i) := by
  unfold softmax sumExp
  have hsum :
      (∑ j : Fin K, Real.exp (x (σ.symm j))) = ∑ j : Fin K, Real.exp (x j) := by
    simpa using
      (Fintype.sum_equiv σ.symm
        (fun j : Fin K => Real.exp (x (σ.symm j)))
        (fun j : Fin K => Real.exp (x j))
        (fun _ => rfl))
  rw [hsum]

theorem expertAttentionHead_smul
    (σ : Equiv.Perm (Fin K)) (p : ExpertAttentionVector V K) :
    expertAttentionHead (σ • p) = expertAttentionHead p := by
  change
    (∑ i : Fin K,
      softmax (fun j => (p (σ.symm j)).1) i • (p (σ.symm i)).2) =
      ∑ i : Fin K, softmax (fun j => (p j).1) i • (p i).2
  calc
    (∑ i : Fin K,
        softmax (fun j => (p (σ.symm j)).1) i • (p (σ.symm i)).2) =
        ∑ i : Fin K, softmax (fun j => (p j).1) (σ.symm i) • (p (σ.symm i)).2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [softmax_reindex σ (fun j => (p j).1) i]
    _ = ∑ i : Fin K, softmax (fun j => (p j).1) i • (p i).2 := by
      simpa using
        (Fintype.sum_equiv σ.symm
          (fun i : Fin K => softmax (fun j => (p j).1) (σ.symm i) • (p (σ.symm i)).2)
          (fun i : Fin K => softmax (fun j => (p j).1) i • (p i).2)
          (fun _ => rfl))

theorem continuous_expertAttentionHead :
    Continuous (expertAttentionHead (V := V) (K := K)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  unfold expertAttentionHead
  apply continuous_finset_sum (s := (Finset.univ : Finset (Fin K)))
  intro i hi
  have hlogits : ∀ j : Fin K,
      Continuous (fun p : ExpertAttentionVector V K => (p j).1) := by
    intro j
    exact continuous_fst.comp (continuous_apply j)
  have hweight : Continuous (fun p : ExpertAttentionVector V K =>
      softmax (fun j => (p j).1) i) :=
    InfoGeometry.Topology.continuous_latentSoftmax_coordinate
      (fun p : ExpertAttentionVector V K => fun j => (p j).1) hlogits i
  have hvalue : Continuous (fun p : ExpertAttentionVector V K => (p i).2) :=
    continuous_snd.comp (continuous_apply i)
  exact hweight.smul hvalue

noncomputable def expertAttentionHeadOnModuli :
    KANModuliSpace (ℝ × V) K → V :=
  invariantLift expertAttentionHead expertAttentionHead_smul

theorem continuous_expertAttentionHeadOnModuli :
    Continuous (expertAttentionHeadOnModuli (V := V) (K := K)) := by
  exact continuous_invariantLift expertAttentionHead
    continuous_expertAttentionHead expertAttentionHead_smul

@[simp] theorem expertAttentionHeadOnModuli_quotientMap
    (p : ExpertAttentionVector V K) :
    expertAttentionHeadOnModuli (V := V) (K := K)
      (quotientMap (V := ℝ × V) (K := K) p) = expertAttentionHead p := by
  exact invariantLift_quotientMap expertAttentionHead expertAttentionHead_smul p

theorem expertAttentionHeadOnModuli_fiber_isClosed
    [T1Space V] (v : V) :
    IsClosed {q : KANModuliSpace (ℝ × V) K |
      expertAttentionHeadOnModuli (V := V) (K := K) q = v} := by
  change IsClosed
    ((expertAttentionHeadOnModuli (V := V) (K := K)) ⁻¹' ({v} : Set V))
  exact isClosed_singleton.preimage
    (continuous_expertAttentionHeadOnModuli (V := V) (K := K))

end InfoGeometry.Canonical.KANModuli

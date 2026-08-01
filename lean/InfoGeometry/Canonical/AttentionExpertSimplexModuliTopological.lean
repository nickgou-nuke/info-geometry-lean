import InfoGeometry.Canonical.AttentionExpertModuliTopological
import Mathlib.Analysis.Convex.StdSimplex
import InfoGeometry.Inference.FiniteGibbsThermodynamicIdentity

open scoped BigOperators

namespace InfoGeometry.Canonical.KANModuli

open InfoGeometry.Convex.LogSumExp

variable {K : ℕ} {V : Type*}
variable [TopologicalSpace V]
variable [Fact (0 < K)]

/-- The ordered softmax responsibility vector attached to expert logits. -/
noncomputable def expertSoftmaxVector
    (p : ExpertAttentionVector V K) : Fin K → ℝ :=
  fun i => softmax (fun j => (p j).1) i

theorem expertSoftmaxVector_smul
    (σ : Equiv.Perm (Fin K)) (p : ExpertAttentionVector V K) :
    expertSoftmaxVector (σ • p) = σ • expertSoftmaxVector p := by
  ext i
  change softmax (fun j => (p (σ.symm j)).1) i =
    softmax (fun j => (p j).1) (σ.symm i)
  exact softmax_reindex σ (fun j => (p j).1) i

theorem expertSoftmaxVector_mem_stdSimplex
    (p : ExpertAttentionVector V K) :
    expertSoftmaxVector p ∈ stdSimplex ℝ (Fin K) := by
  letI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  exact InfoGeometry.Topology.latentSoftmax_mem_stdSimplex
    (fun _ : ExpertAttentionVector V K => fun j => (p j).1) p

theorem continuous_expertSoftmaxVector :
    Continuous (expertSoftmaxVector (V := V) (K := K)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  apply continuous_pi
  intro i
  have hlogits : ∀ j : Fin K,
      Continuous (fun p : ExpertAttentionVector V K => (p j).1) := by
    intro j
    exact continuous_fst.comp (continuous_apply j)
  exact InfoGeometry.Topology.continuous_latentSoftmax_coordinate
    (fun p : ExpertAttentionVector V K => fun j => (p j).1) hlogits i

/-- Ordered logits are sent to an unordered softmax orbit.  The quotient
target is essential: relabelling experts relabels coordinates of the vector. -/
noncomputable def expertSoftmaxOrbitReadout
    (p : ExpertAttentionVector V K) : KANModuliSpace ℝ K :=
  quotientMap (V := ℝ) (K := K) (expertSoftmaxVector p)

theorem expertSoftmaxOrbitReadout_smul
    (σ : Equiv.Perm (Fin K)) (p : ExpertAttentionVector V K) :
    expertSoftmaxOrbitReadout (σ • p) = expertSoftmaxOrbitReadout p := by
  unfold expertSoftmaxOrbitReadout
  rw [expertSoftmaxVector_smul]
  exact Quotient.sound ⟨σ, rfl⟩

theorem continuous_expertSoftmaxOrbitReadout :
    Continuous (expertSoftmaxOrbitReadout (V := V) (K := K)) := by
  exact continuous_quotientMap.comp continuous_expertSoftmaxVector

/-- Gauge-descended symbolic latent map into the unordered softmax quotient. -/
noncomputable def expertSoftmaxOnModuli :
    KANModuliSpace (ℝ × V) K → KANModuliSpace ℝ K :=
  invariantLift expertSoftmaxOrbitReadout expertSoftmaxOrbitReadout_smul

theorem continuous_expertSoftmaxOnModuli :
    Continuous (expertSoftmaxOnModuli (V := V) (K := K)) := by
  exact continuous_invariantLift expertSoftmaxOrbitReadout
    continuous_expertSoftmaxOrbitReadout expertSoftmaxOrbitReadout_smul

@[simp] theorem expertSoftmaxOnModuli_quotientMap
    (p : ExpertAttentionVector V K) :
    expertSoftmaxOnModuli (V := V) (K := K)
      (quotientMap (V := ℝ × V) (K := K) p) =
        expertSoftmaxOrbitReadout p := by
  exact invariantLift_quotientMap expertSoftmaxOrbitReadout
    expertSoftmaxOrbitReadout_smul p

/-- A symmetric concentration observable of the latent responsibility vector. -/
noncomputable def expertSoftmaxConcentration
    (p : ExpertAttentionVector V K) : ℝ :=
  ∑ i : Fin K, (softmax (fun j => (p j).1) i) ^ 2

theorem expertSoftmaxConcentration_smul
    (σ : Equiv.Perm (Fin K)) (p : ExpertAttentionVector V K) :
    expertSoftmaxConcentration (σ • p) = expertSoftmaxConcentration p := by
  change
    (∑ i : Fin K, (softmax (fun j => (p (σ.symm j)).1) i) ^ 2) =
      ∑ i : Fin K, (softmax (fun j => (p j).1) i) ^ 2
  calc
    (∑ i : Fin K, (softmax (fun j => (p (σ.symm j)).1) i) ^ 2) =
        ∑ i : Fin K, (softmax (fun j => (p j).1) (σ.symm i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [softmax_reindex σ (fun j => (p j).1) i]
    _ = ∑ i : Fin K, (softmax (fun j => (p j).1) i) ^ 2 := by
      simpa using
        (Fintype.sum_equiv σ.symm
          (fun i : Fin K => (softmax (fun j => (p j).1) (σ.symm i)) ^ 2)
          (fun i : Fin K => (softmax (fun j => (p j).1) i) ^ 2)
          (fun _ => rfl))

theorem continuous_expertSoftmaxConcentration :
    Continuous (expertSoftmaxConcentration (V := V) (K := K)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  unfold expertSoftmaxConcentration
  apply continuous_finset_sum
  intro i hi
  have hlogits : ∀ j : Fin K,
      Continuous (fun p : ExpertAttentionVector V K => (p j).1) := by
    intro j
    exact continuous_fst.comp (continuous_apply j)
  have hweight : Continuous (fun p : ExpertAttentionVector V K =>
      softmax (fun j => (p j).1) i) :=
    InfoGeometry.Topology.continuous_latentSoftmax_coordinate
      (fun p : ExpertAttentionVector V K => fun j => (p j).1) hlogits i
  exact hweight.pow 2

/-- The concentration descends as a scalar observable on the gauge quotient. -/
noncomputable def expertSoftmaxConcentrationOnModuli :
    KANModuliSpace (ℝ × V) K → ℝ :=
  invariantLift expertSoftmaxConcentration expertSoftmaxConcentration_smul

theorem continuous_expertSoftmaxConcentrationOnModuli :
    Continuous (expertSoftmaxConcentrationOnModuli (V := V) (K := K)) := by
  exact continuous_invariantLift expertSoftmaxConcentration
    continuous_expertSoftmaxConcentration expertSoftmaxConcentration_smul

theorem expertSoftmaxConcentrationOnModuli_levelSet_isClosed (c : ℝ) :
    IsClosed {q : KANModuliSpace (ℝ × V) K |
      expertSoftmaxConcentrationOnModuli (V := V) (K := K) q = c} := by
  change IsClosed
    ((expertSoftmaxConcentrationOnModuli (V := V) (K := K)) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_expertSoftmaxConcentrationOnModuli (V := V) (K := K))

theorem expertSoftmaxConcentrationOnModuli_sublevel_isClosed (c : ℝ) :
    IsClosed {q : KANModuliSpace (ℝ × V) K |
      expertSoftmaxConcentrationOnModuli (V := V) (K := K) q ≤ c} := by
  change IsClosed
    ((expertSoftmaxConcentrationOnModuli (V := V) (K := K)) ⁻¹' (Set.Iic c))
  exact isClosed_Iic.preimage
    (continuous_expertSoftmaxConcentrationOnModuli (V := V) (K := K))

/-! ### Entropy observable

The concentration above is a polynomial symmetric readout.  The next
observable is the ordinary Shannon entropy of the strictly positive softmax
vector.  Positivity is used explicitly, so the logarithm is never extended
to a boundary value by convention.
-/

noncomputable def expertSoftmaxEntropy
    (p : ExpertAttentionVector V K) : ℝ :=
  -∑ i : Fin K,
      (softmax (fun j => (p j).1) i) *
        Real.log (softmax (fun j => (p j).1) i)

theorem expertSoftmaxEntropy_smul
    (σ : Equiv.Perm (Fin K)) (p : ExpertAttentionVector V K) :
    expertSoftmaxEntropy (σ • p) = expertSoftmaxEntropy p := by
  change
    -∑ i : Fin K,
        (softmax (fun j => (p (σ.symm j)).1) i) *
          Real.log (softmax (fun j => (p (σ.symm j)).1) i) =
      -∑ i : Fin K,
        (softmax (fun j => (p j).1) i) *
          Real.log (softmax (fun j => (p j).1) i)
  congr 1
  calc
    (∑ i : Fin K,
        (softmax (fun j => (p (σ.symm j)).1) i) *
          Real.log (softmax (fun j => (p (σ.symm j)).1) i)) =
        ∑ i : Fin K,
          (softmax (fun j => (p j).1) (σ.symm i)) *
            Real.log (softmax (fun j => (p j).1) (σ.symm i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [softmax_reindex σ (fun j => (p j).1) i]
    _ = ∑ i : Fin K,
          (softmax (fun j => (p j).1) i) *
            Real.log (softmax (fun j => (p j).1) i) := by
      simpa using
        (Fintype.sum_equiv σ.symm
          (fun i : Fin K =>
            (softmax (fun j => (p j).1) (σ.symm i)) *
              Real.log (softmax (fun j => (p j).1) (σ.symm i)))
          (fun i : Fin K =>
            (softmax (fun j => (p j).1) i) *
              Real.log (softmax (fun j => (p j).1) i))
          (fun _ => rfl))

theorem continuous_expertSoftmaxEntropy :
    Continuous (expertSoftmaxEntropy (V := V) (K := K)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  unfold expertSoftmaxEntropy
  apply Continuous.neg
  apply continuous_finset_sum
  intro i hi
  have hlogits : ∀ j : Fin K,
      Continuous (fun p : ExpertAttentionVector V K => (p j).1) := by
    intro j
    exact continuous_fst.comp (continuous_apply j)
  have hweight : Continuous (fun p : ExpertAttentionVector V K =>
      softmax (fun j => (p j).1) i) :=
    InfoGeometry.Topology.continuous_latentSoftmax_coordinate
      (fun p : ExpertAttentionVector V K => fun j => (p j).1) hlogits i
  have hweight_ne : ∀ p : ExpertAttentionVector V K,
      softmax (fun j => (p j).1) i ≠ 0 := by
    intro p
    unfold softmax
    exact (div_pos (Real.exp_pos _) (sumExp_pos _)).ne'
  exact hweight.mul (hweight.log hweight_ne)

noncomputable def expertSoftmaxEntropyOnModuli :
    KANModuliSpace (ℝ × V) K → ℝ :=
  invariantLift expertSoftmaxEntropy expertSoftmaxEntropy_smul

theorem continuous_expertSoftmaxEntropyOnModuli :
    Continuous (expertSoftmaxEntropyOnModuli (V := V) (K := K)) := by
  exact continuous_invariantLift expertSoftmaxEntropy
    continuous_expertSoftmaxEntropy expertSoftmaxEntropy_smul

theorem expertSoftmaxEntropyOnModuli_levelSet_isClosed (c : ℝ) :
    IsClosed {q : KANModuliSpace (ℝ × V) K |
      expertSoftmaxEntropyOnModuli (V := V) (K := K) q = c} := by
  change IsClosed
    ((expertSoftmaxEntropyOnModuli (V := V) (K := K)) ⁻¹' ({c} : Set ℝ))
  exact isClosed_singleton.preimage
    (continuous_expertSoftmaxEntropyOnModuli (V := V) (K := K))

theorem expertSoftmaxEntropyOnModuli_superlevel_isClosed (c : ℝ) :
    IsClosed {q : KANModuliSpace (ℝ × V) K |
      c ≤ expertSoftmaxEntropyOnModuli (V := V) (K := K) q} := by
  change IsClosed
    ((expertSoftmaxEntropyOnModuli (V := V) (K := K)) ⁻¹' (Set.Ici c))
  exact isClosed_Ici.preimage
    (continuous_expertSoftmaxEntropyOnModuli (V := V) (K := K))

theorem expertSoftmaxEntropy_bounds
    (p : ExpertAttentionVector V K) :
    0 ≤ expertSoftmaxEntropy p ∧
      expertSoftmaxEntropy p ≤ Real.log (Fintype.card (Fin K)) := by
  letI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  let q : Fin K → ℝ := expertSoftmaxVector p
  have hq_pos : ∀ i : Fin K, 0 < q i := by
    intro i
    dsimp [q, expertSoftmaxVector]
    unfold softmax
    exact div_pos (Real.exp_pos _) (sumExp_pos _)
  have hq_sum : ∑ i : Fin K, q i = 1 := by
    exact sum_softmax_eq_one _
  have hnonneg := InfoGeometry.Inference.FiniteGibbs.entropyOf_nonneg q hq_pos hq_sum
  have hupper := InfoGeometry.Inference.FiniteGibbs.entropyOf_le_log_card q hq_pos hq_sum
  exact ⟨by simpa [q, expertSoftmaxEntropy, expertSoftmaxVector,
      InfoGeometry.Inference.FiniteGibbs.entropyOf] using hnonneg,
    by simpa [q, expertSoftmaxEntropy, expertSoftmaxVector,
      InfoGeometry.Inference.FiniteGibbs.entropyOf] using hupper⟩

end InfoGeometry.Canonical.KANModuli

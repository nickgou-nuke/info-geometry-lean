import InfoGeometry.Canonical.KANModuliTopology

namespace InfoGeometry.Canonical.KANModuli

variable {K : ℕ} {V : Type*} [TopologicalSpace V]

/--
The quotient-level readout of a finite routing loss.

This definition does not assert that a particular unbalanced optimal-transport
minimum has already been formalized.  It applies to any concrete finite loss
whose continuity and permutation invariance have been proved separately.
-/
def sinkhornRoutingLossOnModuli
    (loss : ExpertVector V K → ℝ)
    (hinv : ∀ (σ : Equiv.Perm (Fin K)) (v : ExpertVector V K),
      loss (σ • v) = loss v) :
    KANModuliSpace V K → ℝ :=
  invariantLift (V := V) (K := K) loss hinv

/--
An invariant continuous finite routing loss descends continuously through the
permutation quotient.

The theorem is conditional on the actual loss supplied by an application; it
does not conflate a finite readout with an analytic Sinkhorn minimization.
-/
theorem continuous_sinkhornRoutingLossOnModuli
    (loss : ExpertVector V K → ℝ)
    (hcont : Continuous loss)
    (hinv : ∀ (σ : Equiv.Perm (Fin K)) (v : ExpertVector V K),
      loss (σ • v) = loss v) :
    Continuous (sinkhornRoutingLossOnModuli (V := V) (K := K) loss hinv) := by
  exact continuous_invariantLift loss hcont hinv

@[simp]
theorem sinkhornRoutingLossOnModuli_quotientMap
    (loss : ExpertVector V K → ℝ)
    (hinv : ∀ (σ : Equiv.Perm (Fin K)) (v : ExpertVector V K),
      loss (σ • v) = loss v)
    (v : ExpertVector V K) :
    sinkhornRoutingLossOnModuli (V := V) (K := K) loss hinv
      (quotientMap (V := V) (K := K) v) = loss v := by
  exact invariantLift_quotientMap loss hinv v

section NormEnergy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A finite permutation-invariant routing energy on expert coordinates. -/
def expertNormEnergy {K : ℕ} : ExpertVector V K → ℝ :=
  fun v => ∑ i : Fin K, ‖v i‖ ^ 2

theorem expertNormEnergy_smul {K : ℕ}
    (σ : Equiv.Perm (Fin K)) (v : ExpertVector V K) :
    expertNormEnergy (σ • v) = expertNormEnergy v := by
  change (∑ i : Fin K, ‖v (σ.symm i)‖ ^ 2) = ∑ i : Fin K, ‖v i‖ ^ 2
  simpa using
    (Fintype.sum_equiv σ.symm
      (fun i : Fin K => ‖v (σ.symm i)‖ ^ 2)
      (fun i : Fin K => ‖v i‖ ^ 2)
      (fun _ => rfl))

theorem continuous_expertNormEnergy {K : ℕ} :
    Continuous (expertNormEnergy (V := V) (K := K)) := by
  unfold expertNormEnergy
  apply continuous_finset_sum
  intro i hi
  exact (continuous_norm.comp (continuous_apply i)).pow 2

def expertNormEnergyOnModuli {K : ℕ} :
    KANModuliSpace V K → ℝ :=
  sinkhornRoutingLossOnModuli expertNormEnergy expertNormEnergy_smul

theorem continuous_expertNormEnergyOnModuli {K : ℕ} :
    Continuous (expertNormEnergyOnModuli (V := V) (K := K)) := by
  exact continuous_sinkhornRoutingLossOnModuli expertNormEnergy
    (continuous_expertNormEnergy (V := V) (K := K)) expertNormEnergy_smul

@[simp]
theorem expertNormEnergyOnModuli_quotientMap {K : ℕ}
    (v : ExpertVector V K) :
    expertNormEnergyOnModuli (V := V) (K := K)
        (quotientMap (V := V) (K := K) v) = expertNormEnergy v := by
  exact sinkhornRoutingLossOnModuli_quotientMap expertNormEnergy
    expertNormEnergy_smul v

theorem expertNormEnergy_nonneg {K : ℕ} (v : ExpertVector V K) :
    0 ≤ expertNormEnergy v := by
  unfold expertNormEnergy
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

theorem expertNormEnergyOnModuli_nonneg {K : ℕ}
    (q : KANModuliSpace V K) :
    0 ≤ expertNormEnergyOnModuli (V := V) (K := K) q := by
  refine Quotient.inductionOn q ?_
  intro v
  simpa only [expertNormEnergyOnModuli_quotientMap] using
    expertNormEnergy_nonneg v

theorem expertNormEnergyOnModuli_sublevel_isClosed {K : ℕ} (c : ℝ) :
    IsClosed {q : KANModuliSpace V K |
      expertNormEnergyOnModuli (V := V) (K := K) q ≤ c} := by
  change IsClosed
    ((expertNormEnergyOnModuli (V := V) (K := K)) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_expertNormEnergyOnModuli (V := V) (K := K))

end NormEnergy

end InfoGeometry.Canonical.KANModuli

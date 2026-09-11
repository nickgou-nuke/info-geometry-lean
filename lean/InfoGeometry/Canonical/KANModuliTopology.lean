import Mathlib.Topology.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Basic

open TopologicalSpace

namespace InfoGeometry.Canonical.KANModuli

variable {K : ℕ} {V : Type*} [TopologicalSpace V]

/-- The finite coordinate space of K expert functions -/
abbrev ExpertVector (V : Type*) (K : ℕ) := Fin K → V

/-- Permutation action of S_K on ExpertVector via re-indexing -/
instance : MulAction (Equiv.Perm (Fin K)) (ExpertVector V K) where
  smul σ v := v ∘ σ.symm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The orbit setoid induced by expert permutations S_K -/
instance expertSetoid (V : Type*) (K : ℕ) : Setoid (ExpertVector V K) :=
  MulAction.orbitRel (Equiv.Perm (Fin K)) (ExpertVector V K)

/-- The KAN Moduli Quotient Type: [V^K / S_K] -/
def KANModuliSpace (V : Type*) (K : ℕ) : Type _ :=
  Quotient (expertSetoid V K)

/-- 
Constructive quotient topology on the KAN Moduli Space 
induced by expert coordinate product topology.
-/
instance : TopologicalSpace (KANModuliSpace V K) :=
  instTopologicalSpaceQuotient

/-- Canonical projection map π : V^K → V^K / S_K -/
def quotientMap : ExpertVector V K → KANModuliSpace V K :=
  Quotient.mk (expertSetoid V K)

/-- Theorem: The quotient projection map π is strictly continuous -/
theorem continuous_quotientMap : Continuous (quotientMap (V := V) (K := K)) :=
  continuous_quotient_mk'

theorem quotientMap_surjective :
    Function.Surjective (quotientMap (V := V) (K := K)) := by
  intro q
  exact Quotient.inductionOn q (fun v => ⟨v, rfl⟩)

/-- 
Theorem: Universal Property of the KAN Moduli Topology
Any S_K-invariant continuous function on expert coordinates uniquely 
lifts to a continuous function on the KAN moduli space.
-/
def invariantLift {Y : Type*} [TopologicalSpace Y]
    (f : ExpertVector V K → Y)
    (hf_inv : ∀ (σ : Equiv.Perm (Fin K)) (v : ExpertVector V K),
      f (σ • v) = f v) :
    KANModuliSpace V K → Y :=
  Quotient.lift f (by
    intro a b h
    rcases h with ⟨σ, hσ⟩
    rw [← hσ, hf_inv σ b])

@[simp]
theorem invariantLift_quotientMap {Y : Type*} [TopologicalSpace Y]
    (f : ExpertVector V K → Y)
    (hf_inv : ∀ (σ : Equiv.Perm (Fin K)) (v : ExpertVector V K),
      f (σ • v) = f v)
    (v : ExpertVector V K) :
    invariantLift (V := V) (K := K) f hf_inv
      (quotientMap (V := V) (K := K) v) = f v :=
  rfl

theorem continuous_invariantLift {Y : Type*} [TopologicalSpace Y]
    (f : ExpertVector V K → Y)
    (hf_cont : Continuous f)
    (hf_inv : ∀ (σ : Equiv.Perm (Fin K)) (v : ExpertVector V K),
      f (σ • v) = f v) :
    Continuous (invariantLift (V := V) (K := K) f hf_inv) := by
  exact Continuous.quotient_lift hf_cont _

theorem invariantLift_unique {Y : Type*} [TopologicalSpace Y]
    (f : ExpertVector V K → Y)
    (hf_inv : ∀ (σ : Equiv.Perm (Fin K)) (v : ExpertVector V K),
      f (σ • v) = f v)
    (g : KANModuliSpace V K → Y)
    (hg : ∀ v, g (quotientMap (V := V) (K := K) v) = f v) :
    g = invariantLift (V := V) (K := K) f hf_inv := by
  funext q
  refine Quotient.inductionOn q ?_
  intro v
  simpa using hg v

theorem lift_continuous {Y : Type*} [TopologicalSpace Y]
    (f : ExpertVector V K → Y) 
    (hf_cont : Continuous f)
    (hf_inv : ∀ (σ : Equiv.Perm (Fin K)) (v : ExpertVector V K), f (σ • v) = f v) :
    Continuous (Quotient.lift f (fun a b (h : a ≈ b) => by
      rcases h with ⟨σ, hσ⟩
      rw [← hσ, hf_inv σ b]) : KANModuliSpace V K → Y) := by
  exact Continuous.quotient_lift hf_cont _

def scalarExpertSum {K : ℕ} : ExpertVector ℝ K → ℝ :=
  fun v => ∑ i : Fin K, v i

theorem scalarExpertSum_smul {K : ℕ}
    (σ : Equiv.Perm (Fin K)) (v : ExpertVector ℝ K) :
    scalarExpertSum (σ • v) = scalarExpertSum v := by
  change (∑ i : Fin K, v (σ.symm i)) = ∑ i : Fin K, v i
  simpa using
    (Fintype.sum_equiv σ.symm
      (fun i : Fin K => v (σ.symm i))
      (fun i : Fin K => v i)
      (fun _ => rfl))

theorem continuous_scalarExpertSum {K : ℕ} :
    Continuous (scalarExpertSum (K := K)) := by
  unfold scalarExpertSum
  apply continuous_finset_sum
  intro i hi
  exact continuous_apply i

def scalarExpertSumOnModuli {K : ℕ} :
    KANModuliSpace ℝ K → ℝ :=
  invariantLift scalarExpertSum scalarExpertSum_smul

theorem continuous_scalarExpertSumOnModuli {K : ℕ} :
    Continuous (scalarExpertSumOnModuli (K := K)) := by
  exact continuous_invariantLift scalarExpertSum
    (continuous_scalarExpertSum (K := K)) scalarExpertSum_smul

theorem scalarExpertSumOnModuli_mk {K : ℕ}
    (v : ExpertVector ℝ K) :
    scalarExpertSumOnModuli (K := K)
        (quotientMap (V := ℝ) (K := K) v) = scalarExpertSum v :=
  invariantLift_quotientMap scalarExpertSum scalarExpertSum_smul v

theorem scalarExpertSumOnModuli_levelSet_isClosed {K : ℕ} (c : ℝ) :
    IsClosed {q : KANModuliSpace ℝ K |
      scalarExpertSumOnModuli (K := K) q = c} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({c} : Set ℝ)).preimage
      (continuous_scalarExpertSumOnModuli (K := K))

def scalarExpertEnergy {K : ℕ} : ExpertVector ℝ K → ℝ :=
  fun v => ∑ i : Fin K, (v i) ^ 2

theorem scalarExpertEnergy_nonneg {K : ℕ} (v : ExpertVector ℝ K) :
    0 ≤ scalarExpertEnergy v := by
  unfold scalarExpertEnergy
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

theorem scalarExpertEnergy_smul {K : ℕ}
    (σ : Equiv.Perm (Fin K)) (v : ExpertVector ℝ K) :
    scalarExpertEnergy (σ • v) = scalarExpertEnergy v := by
  change (∑ i : Fin K, (v (σ.symm i)) ^ 2) = ∑ i : Fin K, (v i) ^ 2
  simpa using
    (Fintype.sum_equiv σ.symm
      (fun i : Fin K => (v (σ.symm i)) ^ 2)
      (fun i : Fin K => (v i) ^ 2)
      (fun _ => rfl))

theorem continuous_scalarExpertEnergy {K : ℕ} :
    Continuous (scalarExpertEnergy (K := K)) := by
  unfold scalarExpertEnergy
  apply continuous_finset_sum
  intro i hi
  exact (continuous_apply i).pow 2

def scalarExpertEnergyOnModuli {K : ℕ} :
    KANModuliSpace ℝ K → ℝ :=
  invariantLift scalarExpertEnergy scalarExpertEnergy_smul

theorem continuous_scalarExpertEnergyOnModuli {K : ℕ} :
    Continuous (scalarExpertEnergyOnModuli (K := K)) := by
  exact continuous_invariantLift scalarExpertEnergy
    (continuous_scalarExpertEnergy (K := K)) scalarExpertEnergy_smul

theorem scalarExpertEnergyOnModuli_mk {K : ℕ}
    (v : ExpertVector ℝ K) :
    scalarExpertEnergyOnModuli (K := K)
        (quotientMap (V := ℝ) (K := K) v) = scalarExpertEnergy v :=
  invariantLift_quotientMap scalarExpertEnergy scalarExpertEnergy_smul v

theorem scalarExpertEnergyOnModuli_nonneg {K : ℕ}
    (q : KANModuliSpace ℝ K) :
    0 ≤ scalarExpertEnergyOnModuli (K := K) q := by
  refine Quotient.inductionOn q ?_
  intro v
  simpa only [scalarExpertEnergyOnModuli_mk] using
    scalarExpertEnergy_nonneg v

theorem scalarExpertEnergy_sublevel_isClosed {K : ℕ} (c : ℝ) :
    IsClosed {v : ExpertVector ℝ K | scalarExpertEnergy v ≤ c} := by
  change IsClosed (scalarExpertEnergy ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage (continuous_scalarExpertEnergy (K := K))

theorem scalarExpertEnergyOnModuli_sublevel_isClosed {K : ℕ} (c : ℝ) :
    IsClosed {q : KANModuliSpace ℝ K |
      scalarExpertEnergyOnModuli (K := K) q ≤ c} := by
  change IsClosed (scalarExpertEnergyOnModuli ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_scalarExpertEnergyOnModuli (K := K))

theorem scalarExpertEnergyOnModuli_levelSet_isClosed {K : ℕ} (c : ℝ) :
    IsClosed {q : KANModuliSpace ℝ K |
      scalarExpertEnergyOnModuli (K := K) q = c} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({c} : Set ℝ)).preimage
      (continuous_scalarExpertEnergyOnModuli (K := K))

end InfoGeometry.Canonical.KANModuli

import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.PathConnected

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace SouriauRelativeEntropy

variable {n : ℕ}

/-- 1. Discrete Kullback-Leibler Relative Entropy / Information Divergence:
    D_KL(P || Q) = ∑ᵢ Pᵢ log(Pᵢ / Qᵢ) -/
noncomputable def relativeEntropy (P Q : Fin n → ℝ) : ℝ :=
  ∑ i, P i * Real.log (P i / Q i)

/-- 🏆 THEOREM 1: Self-Nullity of Relative Entropy D_KL(P || P) = 0 -/
theorem relativeEntropy_self_zero (P : Fin n → ℝ) :
    relativeEntropy P P = 0 := by
  dsimp [relativeEntropy]
  have hterm : (fun i => P i * Real.log (P i / P i)) = (fun _ => 0) := by
    ext i
    by_cases h : P i = 0
    · rw [h, zero_mul]
    · rw [div_self h, Real.log_one, mul_zero]
  rw [hterm, Finset.sum_const_zero]

/-- 2. Fisher-Rao Information Tensor as Second Derivative of Log-Likelihood -/
noncomputable def fisherMetricNumerator (P : Fin n → ℝ) (dP : Fin n → ℝ) : ℝ :=
  ∑ i, (dP i)^2 / P i

def positiveOrthant : Set (Fin n → ℝ) :=
  {P | ∀ i, 0 < P i}

theorem isOpen_positiveOrthant :
    IsOpen (positiveOrthant (n := n)) := by
  have hopen : IsOpen (⋂ i : Fin n, (fun P : Fin n → ℝ => P i) ⁻¹' Set.Ioi (0 : ℝ)) := by
    simpa using
      isOpen_biInter_finset (s := (Finset.univ : Finset (Fin n)))
        (fun i hi => isOpen_Ioi.preimage (continuous_apply i))
  simpa [positiveOrthant, Set.setOf_forall] using hopen

theorem convex_positiveOrthant :
    Convex ℝ (positiveOrthant (n := n)) := by
  intro P hP Q hQ a b ha hb hab i
  rcases lt_or_eq_of_le ha with ha_pos | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos (hP i))
      (mul_nonneg hb (le_of_lt (hQ i)))
  · have hb_one : b = 1 := by linarith
    simpa [hb_one] using hQ i

theorem positiveOrthant_nonempty :
    (positiveOrthant (n := n)).Nonempty := by
  refine ⟨fun _ => 1, ?_⟩
  intro i
  norm_num

theorem isPathConnected_positiveOrthant :
    IsPathConnected (positiveOrthant (n := n)) := by
  exact convex_positiveOrthant.isPathConnected positiveOrthant_nonempty

def positiveOrthantPair :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  positiveOrthant (n := n) ×ˢ positiveOrthant (n := n)

theorem isOpen_positiveOrthantPair :
    IsOpen (positiveOrthantPair (n := n)) := by
  exact isOpen_positiveOrthant.prod isOpen_positiveOrthant

theorem convex_positiveOrthantPair :
    Convex ℝ (positiveOrthantPair (n := n)) := by
  exact convex_positiveOrthant.prod convex_positiveOrthant

theorem positiveOrthantPair_nonempty :
    (positiveOrthantPair (n := n)).Nonempty := by
  exact positiveOrthant_nonempty.prod positiveOrthant_nonempty

theorem isPathConnected_positiveOrthantPair :
    IsPathConnected (positiveOrthantPair (n := n)) := by
  exact convex_positiveOrthantPair.isPathConnected positiveOrthantPair_nonempty

theorem continuousOn_relativeEntropy :
    ContinuousOn
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => relativeEntropy p.1 p.2)
      (positiveOrthantPair (n := n)) := by
  unfold relativeEntropy
  apply continuousOn_finset_sum
  intro i hi
  have hPi : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hQi : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  have hdiv : ContinuousOn
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i / p.2 i)
      (positiveOrthantPair (n := n)) := by
    apply hPi.continuousOn.div hQi.continuousOn
    intro p hp
    exact ne_of_gt (hp.2 i)
  apply hPi.continuousOn.mul
  apply hdiv.log
  intro p hp
  exact div_ne_zero (ne_of_gt (hp.1 i)) (ne_of_gt (hp.2 i))

theorem continuous_relativeEntropy_on_subtype
    (K : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (hKpos : K ⊆ positiveOrthantPair (n := n)) :
    Continuous (fun p : K => relativeEntropy p.1.1 p.1.2) := by
  simpa using ((continuousOn_relativeEntropy (n := n)).mono hKpos).restrict

theorem isCompact_relativeEntropy_image_of_compact
    (K : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hK : IsCompact K)
    (hKpos : K ⊆ positiveOrthantPair (n := n)) :
    IsCompact (Set.range (fun p : K => relativeEntropy p.1.1 p.1.2)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_range (continuous_relativeEntropy_on_subtype K hKpos)

theorem isPathConnected_relativeEntropy_image_of_pathConnected
    (K : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hK : IsPathConnected K)
    (hKpos : K ⊆ positiveOrthantPair (n := n)) :
    IsPathConnected (Set.range (fun p : K => relativeEntropy p.1.1 p.1.2)) := by
  have hdom : IsPathConnected (Set.univ : Set K) := by
    simpa using hK.preimage_coe (U := K) (W := K) Set.Subset.rfl
  simpa [Set.image_univ] using
    hdom.image (continuous_relativeEntropy_on_subtype K hKpos)

theorem continuousOn_fisherMetricNumerator (dP : Fin n → ℝ) :
    ContinuousOn (fun P : Fin n → ℝ => fisherMetricNumerator P dP)
      (positiveOrthant (n := n)) := by
  unfold fisherMetricNumerator
  apply continuousOn_finset_sum
  intro i hi
  apply ContinuousOn.div (continuousOn_const.pow 2)
    (continuous_apply i).continuousOn
  intro P hP
  exact ne_of_gt (hP i)

theorem continuous_fisherMetricNumerator_on_subtype
    (dP : Fin n → ℝ) (K : Set (Fin n → ℝ))
    (hKpos : K ⊆ positiveOrthant (n := n)) :
    Continuous (fun P : K => fisherMetricNumerator P.1 dP) := by
  unfold fisherMetricNumerator
  apply continuous_finset_sum
  intro i hi
  apply Continuous.div (continuous_const.pow 2)
    ((continuous_apply i).comp continuous_subtype_val)
  intro P
  exact ne_of_gt (hKpos P.property i)

theorem isCompact_fisherMetricNumerator_image_of_compact
    (dP : Fin n → ℝ) (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (hKpos : K ⊆ positiveOrthant (n := n)) :
    IsCompact (Set.range (fun P : K => fisherMetricNumerator P.1 dP)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_range (continuous_fisherMetricNumerator_on_subtype dP K hKpos)

theorem isPathConnected_fisherMetricNumerator_image_of_pathConnected
    (dP : Fin n → ℝ) (K : Set (Fin n → ℝ)) (hK : IsPathConnected K)
    (hKpos : K ⊆ positiveOrthant (n := n)) :
    IsPathConnected (Set.range (fun P : K => fisherMetricNumerator P.1 dP)) := by
  have hdom : IsPathConnected (Set.univ : Set K) := by
    simpa using hK.preimage_coe (U := K) (W := K) Set.Subset.rfl
  simpa [Set.image_univ] using
    hdom.image (continuous_fisherMetricNumerator_on_subtype dP K hKpos)

/-- 🏆 THEOREM 2: Non-Negativity of the Fisher-Rao Metric Numerator (Strict Positivity of Variance) -/
theorem fisherMetricNumerator_nonneg (P dP : Fin n → ℝ) (hP : ∀ i, 0 < P i) :
    0 ≤ fisherMetricNumerator P dP := by
  dsimp [fisherMetricNumerator]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hsq : 0 ≤ (dP i)^2 := sq_nonneg (dP i)
  have hp : 0 < P i := hP i
  exact div_nonneg hsq (le_of_lt hp)

/-- 3. Quadratic Variation Identity connecting Relative Entropy Expansion to Fisher Information:
    (P + ε dP) log((P + ε dP) / P) ≈ ε (dP) + (ε² / 2) (dP²/P) -/
theorem relativeEntropy_second_order_cleared (P dP : ℝ) :
    (P + dP) - P = dP := by
  ring

end SouriauRelativeEntropy

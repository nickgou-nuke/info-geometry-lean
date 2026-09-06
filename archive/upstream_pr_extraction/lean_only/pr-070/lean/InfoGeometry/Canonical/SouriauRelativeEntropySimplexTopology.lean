import InfoGeometry.Canonical.SouriauRelativeEntropyFisherBridge
import InfoGeometry.Canonical.SouriauWassersteinGradientFlow
import InfoGeometry.Probability.FiniteGibbsVariational

open BigOperators

namespace SouriauRelativeEntropySimplex

open SouriauRelativeEntropy SouriauWasserstein
open InfoGeometry.Probability.FiniteGibbsVariational

variable {n : ℕ}

/-- The compact part of the probability simplex bounded away from its boundary. -/
def positiveSimplexCore (ε : ℝ) : Set (Fin n → ℝ) :=
  {P | P ∈ probabilitySimplex (n := n) ∧ ∀ i, ε ≤ P i}

theorem isClosed_positiveSimplexCore (ε : ℝ) :
    IsClosed (positiveSimplexCore (n := n) ε) := by
  have hlower : IsClosed {P : Fin n → ℝ | ∀ i, ε ≤ P i} := by
    simpa only [Set.setOf_forall] using
      isClosed_iInter (fun i => isClosed_Ici.preimage (continuous_apply i))
  simpa [positiveSimplexCore, Set.setOf_and] using
    (isClosed_probabilitySimplex (n := n)).inter hlower

theorem isCompact_positiveSimplexCore (ε : ℝ) :
    IsCompact (positiveSimplexCore (n := n) ε) := by
  apply (isCompact_probabilitySimplex (n := n)).of_isClosed_subset
    (isClosed_positiveSimplexCore ε)
  intro P hP
  exact hP.1

theorem convex_positiveSimplexCore (ε : ℝ) :
    Convex ℝ (positiveSimplexCore (n := n) ε) := by
  intro P hP Q hQ a b ha hb hab
  constructor
  · exact convex_probabilitySimplex hP.1 hQ.1 ha hb hab
  · intro i
    change ε ≤ a * P i + b * Q i
    calc
      ε = a * ε + b * ε := by
        rw [← add_mul, hab, one_mul]
      _ ≤ a * P i + b * Q i :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hP.2 i) ha)
          (mul_le_mul_of_nonneg_left (hQ.2 i) hb)

theorem positiveSimplexCore_nonempty
    (hn : 0 < n) {ε : ℝ} (hε : ε ≤ (n : ℝ)⁻¹) :
    (positiveSimplexCore (n := n) ε).Nonempty := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  let P : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  refine ⟨P, ?_⟩
  constructor
  · constructor
    · intro i
      positivity
    · simp [P, Finset.card_univ, hnR]
  · intro i
    exact hε

theorem isPathConnected_positiveSimplexCore
    (hn : 0 < n) {ε : ℝ} (hε : ε ≤ (n : ℝ)⁻¹) :
    IsPathConnected (positiveSimplexCore (n := n) ε) := by
  exact (convex_positiveSimplexCore ε).isPathConnected
    (positiveSimplexCore_nonempty hn hε)

theorem positiveSimplexCore_subset_positiveOrthant
    {ε : ℝ} (hε : 0 < ε) :
    positiveSimplexCore (n := n) ε ⊆ positiveOrthant (n := n) := by
  intro P hP i
  exact lt_of_lt_of_le hε (hP.2 i)

/-- Pairs of probability vectors in the same compact positive simplex core. -/
def positiveSimplexCorePair (ε : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  positiveSimplexCore (n := n) ε ×ˢ positiveSimplexCore (n := n) ε

theorem isCompact_positiveSimplexCorePair (ε : ℝ) :
    IsCompact (positiveSimplexCorePair (n := n) ε) := by
  exact (isCompact_positiveSimplexCore ε).prod
    (isCompact_positiveSimplexCore ε)

theorem isPathConnected_positiveSimplexCorePair
    (hn : 0 < n) {ε : ℝ} (hε : ε ≤ (n : ℝ)⁻¹) :
    IsPathConnected (positiveSimplexCorePair (n := n) ε) := by
  exact ((convex_positiveSimplexCore ε).prod
    (convex_positiveSimplexCore ε)).isPathConnected
      ((positiveSimplexCore_nonempty hn hε).prod
        (positiveSimplexCore_nonempty hn hε))

theorem positiveSimplexCorePair_subset_positiveOrthantPair
    {ε : ℝ} (hε : 0 < ε) :
    positiveSimplexCorePair (n := n) ε ⊆
      positiveOrthantPair (n := n) := by
  exact Set.prod_mono
    (positiveSimplexCore_subset_positiveOrthant hε)
    (positiveSimplexCore_subset_positiveOrthant hε)

def relativeEntropyCoreRange (ε : ℝ) : Set ℝ :=
  Set.range
    (fun p : positiveSimplexCorePair (n := n) ε =>
      relativeEntropy p.1.1 p.1.2)

theorem isClosed_relativeEntropy_level_set_on_positiveSimplexCorePair
    {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    IsClosed {p : positiveSimplexCorePair (n := n) ε |
      relativeEntropy p.1.1 p.1.2 = c} := by
  exact isClosed_singleton.preimage
    (continuous_relativeEntropy_on_subtype _
      (positiveSimplexCorePair_subset_positiveOrthantPair hε))

theorem isCompact_relativeEntropy_image_on_positiveSimplexCorePair
    {ε : ℝ} (hε : 0 < ε) :
    IsCompact (relativeEntropyCoreRange (n := n) ε) := by
  exact isCompact_relativeEntropy_image_of_compact _
    (isCompact_positiveSimplexCorePair ε)
    (positiveSimplexCorePair_subset_positiveOrthantPair hε)

theorem isPathConnected_relativeEntropy_image_on_positiveSimplexCorePair
    (hn : 0 < n) {ε : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    IsPathConnected (relativeEntropyCoreRange (n := n) ε) := by
  exact isPathConnected_relativeEntropy_image_of_pathConnected _
    (isPathConnected_positiveSimplexCorePair hn hεupper)
    (positiveSimplexCorePair_subset_positiveOrthantPair hεpos)

theorem ordConnected_relativeEntropy_image_on_positiveSimplexCorePair
    (hn : 0 < n) {ε : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    (relativeEntropyCoreRange (n := n) ε).OrdConnected := by
  exact
    (isPathConnected_relativeEntropy_image_on_positiveSimplexCorePair
      hn hεpos hεupper).isConnected.isPreconnected.ordConnected

theorem relativeEntropyCoreRange_nonempty
    (hn : 0 < n) {ε : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    (relativeEntropyCoreRange (n := n) ε).Nonempty := by
  exact
    (isPathConnected_relativeEntropy_image_on_positiveSimplexCorePair
      hn hεpos hεupper).nonempty

theorem relativeEntropy_nonneg_on_positiveSimplexCorePair
    {ε : ℝ} (hεpos : 0 < ε)
    (p : positiveSimplexCorePair (n := n) ε) :
    0 ≤ relativeEntropy p.1.1 p.1.2 := by
  have hp : ∀ i, 0 < p.1.1 i :=
    positiveSimplexCore_subset_positiveOrthant hεpos p.property.1
  have hq : ∀ i, 0 < p.1.2 i :=
    positiveSimplexCore_subset_positiveOrthant hεpos p.property.2
  simpa [relativeEntropy, finiteRelativeEntropy] using
    finiteRelativeEntropy_nonneg p.1.1 p.1.2 hp hq
      p.property.1.1.2 p.property.2.1.2

theorem positiveSimplexCore_coord_le_one
    {ε : ℝ} {P : Fin n → ℝ}
    (hP : P ∈ positiveSimplexCore (n := n) ε) (i : Fin n) :
    P i ≤ 1 := by
  have hle : P i ≤ ∑ j : Fin n, P j :=
    Finset.single_le_sum (fun j _ => hP.1.1 j) (Finset.mem_univ i)
  simpa [hP.1.2] using hle

theorem relativeEntropy_le_log_inv_epsilon_on_positiveSimplexCorePair
    {ε : ℝ} (hεpos : 0 < ε)
    (p : positiveSimplexCorePair (n := n) ε) :
    relativeEntropy p.1.1 p.1.2 ≤ Real.log (1 / ε) := by
  unfold relativeEntropy
  calc
    (∑ i, p.1.1 i * Real.log (p.1.1 i / p.1.2 i)) ≤
        ∑ i, p.1.1 i * Real.log (1 / ε) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp_nonneg : 0 ≤ p.1.1 i := p.property.1.1.1 i
      have hp_le_one : p.1.1 i ≤ 1 :=
        positiveSimplexCore_coord_le_one p.property.1 i
      have hq_pos : 0 < p.1.2 i :=
        lt_of_lt_of_le hεpos (p.property.2.2 i)
      have hratio_pos : 0 < p.1.1 i / p.1.2 i :=
        div_pos (lt_of_lt_of_le hεpos (p.property.1.2 i)) hq_pos
      have hratio_le : p.1.1 i / p.1.2 i ≤ 1 / ε := by
        apply (div_le_div_iff₀ hq_pos hεpos).2
        calc
          p.1.1 i * ε ≤ 1 * ε :=
            mul_le_mul_of_nonneg_right hp_le_one hεpos.le
          _ ≤ 1 * p.1.2 i :=
            mul_le_mul_of_nonneg_left (p.property.2.2 i) zero_le_one
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log hratio_pos hratio_le) hp_nonneg
    _ = (∑ i, p.1.1 i) * Real.log (1 / ε) := by
      rw [Finset.sum_mul]
    _ = Real.log (1 / ε) := by
      rw [p.property.1.1.2, one_mul]

theorem relativeEntropy_eq_zero_iff_on_positiveSimplexCorePair
    {ε : ℝ} (hεpos : 0 < ε)
    (p : positiveSimplexCorePair (n := n) ε) :
    relativeEntropy p.1.1 p.1.2 = 0 ↔ p.1.1 = p.1.2 := by
  have hp : ∀ i, 0 < p.1.1 i :=
    positiveSimplexCore_subset_positiveOrthant hεpos p.property.1
  have hq : ∀ i, 0 < p.1.2 i :=
    positiveSimplexCore_subset_positiveOrthant hεpos p.property.2
  simpa [relativeEntropy, finiteRelativeEntropy] using
    finiteRelativeEntropy_eq_zero_iff p.1.1 p.1.2 hp hq
      p.property.1.1.2 p.property.2.1.2

theorem zero_mem_relativeEntropyCoreRange
    (hn : 0 < n) {ε : ℝ} (hεupper : ε ≤ (n : ℝ)⁻¹) :
    0 ∈ relativeEntropyCoreRange (n := n) ε := by
  rcases positiveSimplexCore_nonempty hn hεupper with ⟨P, hP⟩
  refine ⟨⟨(P, P), hP, hP⟩, ?_⟩
  exact relativeEntropy_self_zero P

theorem relativeEntropyCoreRange_eq_Icc_sInf_sSup
    (hn : 0 < n) {ε : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    relativeEntropyCoreRange (n := n) ε =
      Set.Icc (sInf (relativeEntropyCoreRange (n := n) ε))
        (sSup (relativeEntropyCoreRange (n := n) ε)) := by
  have hcompact :=
    isCompact_relativeEntropy_image_on_positiveSimplexCorePair
      (n := n) hεpos
  have hnonempty :=
    relativeEntropyCoreRange_nonempty hn hεpos hεupper
  have hleast := hcompact.isLeast_sInf hnonempty
  have hgreatest := hcompact.isGreatest_sSup hnonempty
  have hord :=
    ordConnected_relativeEntropy_image_on_positiveSimplexCorePair
      hn hεpos hεupper
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hleast.2 hx, hgreatest.2 hx⟩
  · intro x hx
    exact hord.out hleast.1 hgreatest.1 hx

theorem sInf_relativeEntropyCoreRange_eq_zero
    (hn : 0 < n) {ε : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    sInf (relativeEntropyCoreRange (n := n) ε) = 0 := by
  have hcompact :=
    isCompact_relativeEntropy_image_on_positiveSimplexCorePair
      (n := n) hεpos
  have hnonempty :=
    relativeEntropyCoreRange_nonempty hn hεpos hεupper
  have hleast := hcompact.isLeast_sInf hnonempty
  apply le_antisymm
  · exact hleast.2 (zero_mem_relativeEntropyCoreRange hn hεupper)
  · rcases hleast.1 with ⟨p, hp⟩
    simpa [← hp] using
      relativeEntropy_nonneg_on_positiveSimplexCorePair hεpos p

theorem relativeEntropyCoreRange_eq_Icc_zero_sSup
    (hn : 0 < n) {ε : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    relativeEntropyCoreRange (n := n) ε =
      Set.Icc 0 (sSup (relativeEntropyCoreRange (n := n) ε)) := by
  rw [← sInf_relativeEntropyCoreRange_eq_zero hn hεpos hεupper]
  exact relativeEntropyCoreRange_eq_Icc_sInf_sSup hn hεpos hεupper

theorem relativeEntropyCoreRange_subset_Icc_zero_log_inv_epsilon
    {ε : ℝ} (hεpos : 0 < ε) :
    relativeEntropyCoreRange (n := n) ε ⊆ Set.Icc 0 (Real.log (1 / ε)) := by
  rintro x ⟨p, rfl⟩
  exact
    ⟨relativeEntropy_nonneg_on_positiveSimplexCorePair hεpos p,
      relativeEntropy_le_log_inv_epsilon_on_positiveSimplexCorePair hεpos p⟩

theorem sSup_relativeEntropyCoreRange_le_log_inv_epsilon
    (hn : 0 < n) {ε : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    sSup (relativeEntropyCoreRange (n := n) ε) ≤ Real.log (1 / ε) := by
  have hcompact :=
    isCompact_relativeEntropy_image_on_positiveSimplexCorePair
      (n := n) hεpos
  have hnonempty :=
    relativeEntropyCoreRange_nonempty hn hεpos hεupper
  have hgreatest := hcompact.isGreatest_sSup hnonempty
  rcases hgreatest.1 with ⟨p, hp⟩
  simpa [← hp] using
    relativeEntropy_le_log_inv_epsilon_on_positiveSimplexCorePair hεpos p

theorem exists_relativeEntropy_minimizer
    (hn : 0 < n) {ε : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    ∃ p : positiveSimplexCorePair (n := n) ε,
      ∀ q : positiveSimplexCorePair (n := n) ε,
        relativeEntropy p.1.1 p.1.2 ≤ relativeEntropy q.1.1 q.1.2 := by
  have hcompact :=
    isCompact_relativeEntropy_image_on_positiveSimplexCorePair
      (n := n) hεpos
  have hnonempty :=
    relativeEntropyCoreRange_nonempty hn hεpos hεupper
  have hleast := hcompact.isLeast_sInf hnonempty
  rcases hleast.1 with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro q
  simpa [hp] using hleast.2 ⟨q, rfl⟩

theorem exists_relativeEntropy_maximizer
    (hn : 0 < n) {ε : ℝ} (hεpos : 0 < ε)
    (hεupper : ε ≤ (n : ℝ)⁻¹) :
    ∃ p : positiveSimplexCorePair (n := n) ε,
      ∀ q : positiveSimplexCorePair (n := n) ε,
        relativeEntropy q.1.1 q.1.2 ≤ relativeEntropy p.1.1 p.1.2 := by
  have hcompact :=
    isCompact_relativeEntropy_image_on_positiveSimplexCorePair
      (n := n) hεpos
  have hnonempty :=
    relativeEntropyCoreRange_nonempty hn hεpos hεupper
  have hgreatest := hcompact.isGreatest_sSup hnonempty
  rcases hgreatest.1 with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro q
  simpa [hp] using hgreatest.2 ⟨q, rfl⟩

end SouriauRelativeEntropySimplex

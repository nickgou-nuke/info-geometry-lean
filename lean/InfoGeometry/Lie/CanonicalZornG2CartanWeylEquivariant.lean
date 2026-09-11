import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant

open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
open InfoGeometry.Lie
open scoped BigOperators

/-- The dual action of the short reflection on real Mellin character parameters. -/
def canonicalShortReflectionDualReal (s : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![ -s 0 + 3 * s 1, s 1 ]

/-- The dual action of the long reflection on real Mellin character parameters. -/
def canonicalLongReflectionDualReal (s : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![ s 0, s 0 - s 1 ]

/-- The dual action of the short reflection on the real charge/moment map. -/
def canonicalShortReflectionChargeReal (J : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![ -J 0, 3 * J 0 + J 1 ]

/-- The dual action of the long reflection on the real charge/moment map. -/
def canonicalLongReflectionChargeReal (J : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![ J 0 + J 1, -J 1 ]

theorem short_pairing_equiv (s J : Fin 2 → ℝ) :
    (∑ i : Fin 2, s i * canonicalShortReflectionChargeReal J i) =
      (∑ i : Fin 2, canonicalShortReflectionDualReal s i * J i) := by
  unfold canonicalShortReflectionChargeReal canonicalShortReflectionDualReal
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
  ring

theorem long_pairing_equiv (s J : Fin 2 → ℝ) :
    (∑ i : Fin 2, s i * canonicalLongReflectionChargeReal J i) =
      (∑ i : Fin 2, canonicalLongReflectionDualReal s i * J i) := by
  unfold canonicalLongReflectionChargeReal canonicalLongReflectionDualReal
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
  ring

/-- A Weyl-equivariant ensemble connects the abstract CartanSouriauDatum 
with the G₂ Weyl group reflections, asserting covariance of the Gibbs kernel. -/
structure WeylEquivariantEnsemble (State : Type*) [Fintype State] [Nonempty State] where
  datum : CartanSouriauDatum State
  shortReflection : State ≃ State
  longReflection : State ≃ State
  moment_short_covariant : ∀ (x : State) (i : Fin 2),
    datum.momentMap (shortReflection x) i = canonicalShortReflectionChargeReal (datum.momentMap x) i
  moment_long_covariant : ∀ (x : State) (i : Fin 2),
    datum.momentMap (longReflection x) i = canonicalLongReflectionChargeReal (datum.momentMap x) i

variable {State : Type*} [Fintype State] [Nonempty State] (W : WeylEquivariantEnsemble State)

theorem realGibbsKernel_short_covariant (beta : Fin 2 → ℝ) (x : State) :
    realGibbsKernel W.datum beta (W.shortReflection x) =
      realGibbsKernel W.datum (canonicalShortReflectionDualReal beta) x := by
  unfold realGibbsKernel realPairingEnergy
  congr 1
  apply neg_inj.mpr
  have h := short_pairing_equiv beta (W.datum.momentMap x)
  have hm : (∑ i : Fin 2, beta i * W.datum.momentMap (W.shortReflection x) i) = ∑ i : Fin 2, beta i * canonicalShortReflectionChargeReal (W.datum.momentMap x) i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [W.moment_short_covariant x i]
  rw [hm]
  exact h

theorem realGibbsKernel_long_covariant (beta : Fin 2 → ℝ) (x : State) :
    realGibbsKernel W.datum beta (W.longReflection x) =
      realGibbsKernel W.datum (canonicalLongReflectionDualReal beta) x := by
  unfold realGibbsKernel realPairingEnergy
  congr 1
  apply neg_inj.mpr
  have h := long_pairing_equiv beta (W.datum.momentMap x)
  have hm : (∑ i : Fin 2, beta i * W.datum.momentMap (W.longReflection x) i) = ∑ i : Fin 2, beta i * canonicalLongReflectionChargeReal (W.datum.momentMap x) i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [W.moment_long_covariant x i]
  rw [hm]
  exact h

theorem realGibbsPartition_short_invariant (beta : Fin 2 → ℝ) :
    realGibbsPartition W.datum (canonicalShortReflectionDualReal beta) =
      realGibbsPartition W.datum beta := by
  unfold realGibbsPartition
  have h := Equiv.sum_comp W.shortReflection (realGibbsKernel W.datum beta)
  change ∑ x, realGibbsKernel W.datum beta (W.shortReflection x) = _ at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  rw [realGibbsKernel_short_covariant W beta x]

theorem realGibbsPartition_long_invariant (beta : Fin 2 → ℝ) :
    realGibbsPartition W.datum (canonicalLongReflectionDualReal beta) =
      realGibbsPartition W.datum beta := by
  unfold realGibbsPartition
  have h := Equiv.sum_comp W.longReflection (realGibbsKernel W.datum beta)
  change ∑ x, realGibbsKernel W.datum beta (W.longReflection x) = _ at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  rw [realGibbsKernel_long_covariant W beta x]

theorem souriauMassieu_short_invariant (beta : Fin 2 → ℝ) :
    souriauMassieu W.datum (canonicalShortReflectionDualReal beta) =
      souriauMassieu W.datum beta := by
  unfold souriauMassieu
  rw [realGibbsPartition_short_invariant]

theorem souriauMassieu_long_invariant (beta : Fin 2 → ℝ) :
    souriauMassieu W.datum (canonicalLongReflectionDualReal beta) =
      souriauMassieu W.datum beta := by
  unfold souriauMassieu
  rw [realGibbsPartition_long_invariant]

theorem realGibbsWeight_short_covariant (beta : Fin 2 → ℝ) (x : State) :
    realGibbsWeight W.datum beta (W.shortReflection x) =
      realGibbsWeight W.datum (canonicalShortReflectionDualReal beta) x := by
  unfold realGibbsWeight
  rw [realGibbsKernel_short_covariant, realGibbsPartition_short_invariant]

theorem realGibbsWeight_long_covariant (beta : Fin 2 → ℝ) (x : State) :
    realGibbsWeight W.datum beta (W.longReflection x) =
      realGibbsWeight W.datum (canonicalLongReflectionDualReal beta) x := by
  unfold realGibbsWeight
  rw [realGibbsKernel_long_covariant, realGibbsPartition_long_invariant]

theorem shortDual_involution (s : Fin 2 → ℝ) :
  canonicalShortReflectionDualReal (canonicalShortReflectionDualReal s) = s := by
  unfold canonicalShortReflectionDualReal
  ext i
  fin_cases i
  · change -(-s 0 + 3 * s 1) + 3 * s 1 = s 0; ring
  · change s 1 = s 1; ring

theorem longDual_involution (s : Fin 2 → ℝ) :
  canonicalLongReflectionDualReal (canonicalLongReflectionDualReal s) = s := by
  unfold canonicalLongReflectionDualReal
  ext i
  fin_cases i
  · change s 0 = s 0; ring
  · change s 0 - (s 0 - s 1) = s 1; ring

theorem realGibbsWeight_short_covariant_inv (beta : Fin 2 → ℝ) (x : State) :
    realGibbsWeight W.datum (canonicalShortReflectionDualReal beta) (W.shortReflection x) =
      realGibbsWeight W.datum beta x := by
  have h := realGibbsWeight_short_covariant W (canonicalShortReflectionDualReal beta) x
  rw [shortDual_involution] at h
  exact h

theorem realGibbsWeight_long_covariant_inv (beta : Fin 2 → ℝ) (x : State) :
    realGibbsWeight W.datum (canonicalLongReflectionDualReal beta) (W.longReflection x) =
      realGibbsWeight W.datum beta x := by
  have h := realGibbsWeight_long_covariant W (canonicalLongReflectionDualReal beta) x
  rw [longDual_involution] at h
  exact h

theorem souriauChargeMean_short_covariant (beta : Fin 2 → ℝ) (i : Fin 2) :
    souriauChargeMean W.datum (canonicalShortReflectionDualReal beta) i =
      canonicalShortReflectionChargeReal (souriauChargeMean W.datum beta) i := by
  unfold souriauChargeMean
  rw [← Equiv.sum_comp W.shortReflection]
  have h_congr : (∑ x, realGibbsWeight W.datum (canonicalShortReflectionDualReal beta) (W.shortReflection x) * W.datum.momentMap (W.shortReflection x) i) =
    ∑ x, realGibbsWeight W.datum beta x * canonicalShortReflectionChargeReal (W.datum.momentMap x) i := by
    apply Finset.sum_congr rfl
    intro x _
    rw [realGibbsWeight_short_covariant_inv W beta x]
    rw [W.moment_short_covariant x i]
  rw [h_congr]
  clear h_congr
  fin_cases i
  · change (∑ x, realGibbsWeight W.datum beta x * (-W.datum.momentMap x 0)) = -∑ x, realGibbsWeight W.datum beta x * W.datum.momentMap x 0
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  · change (∑ x, realGibbsWeight W.datum beta x * (3 * W.datum.momentMap x 0 + W.datum.momentMap x 1)) = 3 * (∑ x, realGibbsWeight W.datum beta x * W.datum.momentMap x 0) + (∑ x, realGibbsWeight W.datum beta x * W.datum.momentMap x 1)
    simp only [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    have h3_inner : ∀ x ∈ Finset.univ, realGibbsWeight W.datum beta x * (3 * W.datum.momentMap x 0) = 3 * (realGibbsWeight W.datum beta x * W.datum.momentMap x 0) := by
      intro x _
      ring
    rw [Finset.sum_congr rfl h3_inner]
    rw [← Finset.mul_sum]

theorem souriauChargeMean_long_covariant (beta : Fin 2 → ℝ) (i : Fin 2) :
    souriauChargeMean W.datum (canonicalLongReflectionDualReal beta) i =
      canonicalLongReflectionChargeReal (souriauChargeMean W.datum beta) i := by
  unfold souriauChargeMean
  rw [← Equiv.sum_comp W.longReflection]
  have h_congr : (∑ x, realGibbsWeight W.datum (canonicalLongReflectionDualReal beta) (W.longReflection x) * W.datum.momentMap (W.longReflection x) i) =
    ∑ x, realGibbsWeight W.datum beta x * canonicalLongReflectionChargeReal (W.datum.momentMap x) i := by
    apply Finset.sum_congr rfl
    intro x _
    rw [realGibbsWeight_long_covariant_inv W beta x]
    rw [W.moment_long_covariant x i]
  rw [h_congr]
  clear h_congr
  fin_cases i
  · change (∑ x, realGibbsWeight W.datum beta x * (W.datum.momentMap x 0 + W.datum.momentMap x 1)) = (∑ x, realGibbsWeight W.datum beta x * W.datum.momentMap x 0) + (∑ x, realGibbsWeight W.datum beta x * W.datum.momentMap x 1)
    simp only [mul_add]
    rw [Finset.sum_add_distrib]
  · change (∑ x, realGibbsWeight W.datum beta x * (-W.datum.momentMap x 1)) = -∑ x, realGibbsWeight W.datum beta x * W.datum.momentMap x 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring

theorem fisherSouriauQuadratic_short_covariant (beta v : Fin 2 → ℝ) :
    fisherSouriauQuadratic W.datum (canonicalShortReflectionDualReal beta) v =
      fisherSouriauQuadratic W.datum beta (canonicalShortReflectionDualReal v) := by
  rw [fisherSouriauQuadratic_eq_directionalVariance, fisherSouriauQuadratic_eq_directionalVariance]
  rw [← Equiv.sum_comp W.shortReflection]
  have h_congr : (∑ x, realGibbsWeight W.datum (canonicalShortReflectionDualReal beta) (W.shortReflection x) * (∑ i, v i * (W.datum.momentMap (W.shortReflection x) i - souriauChargeMean W.datum (canonicalShortReflectionDualReal beta) i)) ^ (2 : ℕ)) =
    ∑ x, realGibbsWeight W.datum beta x * (∑ i, canonicalShortReflectionDualReal v i * (W.datum.momentMap x i - souriauChargeMean W.datum beta i)) ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [realGibbsWeight_short_covariant_inv W beta x]
    congr 1
    congr 1
    have h1 := short_pairing_equiv v (W.datum.momentMap x)
    have h2 := short_pairing_equiv v (souriauChargeMean W.datum beta)
    have h3 : (∑ i, v i * W.datum.momentMap (W.shortReflection x) i) = ∑ i, v i * canonicalShortReflectionChargeReal (W.datum.momentMap x) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [W.moment_short_covariant x i]
    have h4 : (∑ i, v i * souriauChargeMean W.datum (canonicalShortReflectionDualReal beta) i) = ∑ i, v i * canonicalShortReflectionChargeReal (souriauChargeMean W.datum beta) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [souriauChargeMean_short_covariant W beta i]
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, h3, h4, h1, h2, ← Finset.sum_sub_distrib]
  rw [h_congr]

theorem fisherSouriauQuadratic_long_covariant (beta v : Fin 2 → ℝ) :
    fisherSouriauQuadratic W.datum (canonicalLongReflectionDualReal beta) v =
      fisherSouriauQuadratic W.datum beta (canonicalLongReflectionDualReal v) := by
  rw [fisherSouriauQuadratic_eq_directionalVariance, fisherSouriauQuadratic_eq_directionalVariance]
  rw [← Equiv.sum_comp W.longReflection]
  have h_congr : (∑ x, realGibbsWeight W.datum (canonicalLongReflectionDualReal beta) (W.longReflection x) * (∑ i, v i * (W.datum.momentMap (W.longReflection x) i - souriauChargeMean W.datum (canonicalLongReflectionDualReal beta) i)) ^ (2 : ℕ)) =
    ∑ x, realGibbsWeight W.datum beta x * (∑ i, canonicalLongReflectionDualReal v i * (W.datum.momentMap x i - souriauChargeMean W.datum beta i)) ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [realGibbsWeight_long_covariant_inv W beta x]
    congr 1
    congr 1
    have h1 := long_pairing_equiv v (W.datum.momentMap x)
    have h2 := long_pairing_equiv v (souriauChargeMean W.datum beta)
    have h3 : (∑ i, v i * W.datum.momentMap (W.longReflection x) i) = ∑ i, v i * canonicalLongReflectionChargeReal (W.datum.momentMap x) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [W.moment_long_covariant x i]
    have h4 : (∑ i, v i * souriauChargeMean W.datum (canonicalLongReflectionDualReal beta) i) = ∑ i, v i * canonicalLongReflectionChargeReal (souriauChargeMean W.datum beta) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [souriauChargeMean_long_covariant W beta i]
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, h3, h4, h1, h2, ← Finset.sum_sub_distrib]
  rw [h_congr]

end InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant

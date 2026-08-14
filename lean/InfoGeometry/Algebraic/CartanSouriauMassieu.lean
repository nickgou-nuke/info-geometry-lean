import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Finite rank-two Souriau/Massieu family

This owner is the finite algebraic/statistical layer for a two-component
charge map.  It deliberately stops before multivariable differentiability and
strict convexity: those require analytic and affine-span hypotheses.  The
closed facts here are positivity of the partition function, normalization of
the Gibbs law, and positive semidefiniteness of the full covariance readout.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CartanSouriauMassieu

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

structure Family (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  charge : ι → Fin 2 → ℝ
  weight_pos : ∀ m, 0 < weight m

def energy (F : Family ι) (β : Fin 2 → ℝ) (m : ι) : ℝ :=
  ∑ a : Fin 2, β a * F.charge m a

def unnormalizedWeight (F : Family ι) (β : Fin 2 → ℝ) (m : ι) : ℝ :=
  F.weight m * Real.exp (-(energy F β m))

def partition (F : Family ι) (β : Fin 2 → ℝ) : ℝ :=
  ∑ m, unnormalizedWeight F β m

def massieu (F : Family ι) (β : Fin 2 → ℝ) : ℝ :=
  Real.log (partition F β)

def probability (F : Family ι) (β : Fin 2 → ℝ) (m : ι) : ℝ :=
  unnormalizedWeight F β m / partition F β

def chargeMean (F : Family ι) (β : Fin 2 → ℝ) (a : Fin 2) : ℝ :=
  ∑ m, probability F β m * F.charge m a

def chargeCovariance (F : Family ι) (β : Fin 2 → ℝ) (a b : Fin 2) : ℝ :=
  ∑ m, probability F β m *
    (F.charge m a - chargeMean F β a) *
    (F.charge m b - chargeMean F β b)

def chargeCovarianceMatrix (F : Family ι) (β : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => chargeCovariance F β a b

def centeredCharge (F : Family ι) (β : Fin 2 → ℝ) (m : ι) (a : Fin 2) : ℝ :=
  F.charge m a - chargeMean F β a

def directionalCenteredCharge
    (F : Family ι) (β v : Fin 2 → ℝ) (m : ι) : ℝ :=
  ∑ a : Fin 2, v a * centeredCharge F β m a

def directionalCharge
    (F : Family ι) (v : Fin 2 → ℝ) (m : ι) : ℝ :=
  ∑ a : Fin 2, v a * F.charge m a

theorem directionalCharge_sub
    (F : Family ι) (v : Fin 2 → ℝ) (m n : ι) :
    directionalCharge F v m - directionalCharge F v n =
      ∑ a : Fin 2, v a * (F.charge m a - F.charge n a) := by
  unfold directionalCharge
  symm
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

theorem unnormalizedWeight_pos (F : Family ι) (β : Fin 2 → ℝ) (m : ι) :
    0 < unnormalizedWeight F β m := by
  unfold unnormalizedWeight
  exact mul_pos (F.weight_pos m) (Real.exp_pos _)

theorem partition_pos (F : Family ι) (β : Fin 2 → ℝ) :
    0 < partition F β := by
  unfold partition
  exact Finset.sum_pos (fun m _hm => unnormalizedWeight_pos F β m)
    Finset.univ_nonempty

theorem massieu_eq_log_partition (F : Family ι) (β : Fin 2 → ℝ) :
  massieu F β = Real.log (partition F β) :=
  rfl

theorem probability_pos (F : Family ι) (β : Fin 2 → ℝ) (m : ι) :
    0 < probability F β m := by
  unfold probability
  exact div_pos (unnormalizedWeight_pos F β m) (partition_pos F β)

theorem probability_sum_one (F : Family ι) (β : Fin 2 → ℝ) :
    ∑ m, probability F β m = 1 := by
  unfold probability partition
  have hne : (∑ m, unnormalizedWeight F β m) ≠ 0 :=
    (partition_pos F β).ne'
  calc
    ∑ m, unnormalizedWeight F β m / ∑ n, unnormalizedWeight F β n =
        (∑ m, unnormalizedWeight F β m) /
          (∑ n, unnormalizedWeight F β n) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset ι))
                (f := fun m => unnormalizedWeight F β m)
                (a := ∑ n, unnormalizedWeight F β n))
    _ = 1 := div_self hne

theorem chargeCovariance_self_eq_expect_sq_sub_sq
    (F : Family ι) (β : Fin 2 → ℝ) (a : Fin 2) :
    chargeCovariance F β a a =
      (∑ m, probability F β m * (F.charge m a) ^ 2) -
        (chargeMean F β a) ^ 2 := by
  have hsum : ∑ m, probability F β m = 1 := probability_sum_one F β
  unfold chargeCovariance chargeMean
  calc
    ∑ m, probability F β m *
        (F.charge m a - ∑ n, probability F β n * F.charge n a) *
        (F.charge m a - ∑ n, probability F β n * F.charge n a) =
      ∑ m, (probability F β m * (F.charge m a)^2 -
        2 * (∑ n, probability F β n * F.charge n a) *
          (probability F β m * F.charge m a) +
        (∑ n, probability F β n * F.charge n a)^2 *
          probability F β m) := by
      apply Finset.sum_congr rfl
      intro m _hm
      ring
    _ = (∑ m, probability F β m * (F.charge m a)^2) -
        (∑ n, probability F β n * F.charge n a)^2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hcross :
          (∑ m, 2 * (∑ n, probability F β n * F.charge n a) *
            (probability F β m * F.charge m a)) =
          2 * (∑ n, probability F β n * F.charge n a) ^ 2 := by
        calc
          (∑ m, 2 * (∑ n, probability F β n * F.charge n a) *
              (probability F β m * F.charge m a)) =
              (2 * (∑ n, probability F β n * F.charge n a)) *
                (∑ m, probability F β m * F.charge m a) := by
            exact (Finset.mul_sum (s := (Finset.univ : Finset ι))
              (a := 2 * (∑ n, probability F β n * F.charge n a))
              (f := fun m => probability F β m * F.charge m a)).symm
          _ = 2 * (∑ n, probability F β n * F.charge n a) ^ 2 := by
            ring
      have hlast :
          (∑ m, (∑ n, probability F β n * F.charge n a) ^ 2 *
            probability F β m) =
          (∑ n, probability F β n * F.charge n a) ^ 2 := by
        rw [← Finset.mul_sum, hsum]
        ring
      rw [hcross, hlast]
      ring

theorem chargeCovariance_self_nonneg
    (F : Family ι) (β : Fin 2 → ℝ) (a : Fin 2) :
    0 ≤ chargeCovariance F β a a := by
  unfold chargeCovariance
  refine Finset.sum_nonneg ?_
  intro m _hm
  have hprob : 0 ≤ probability F β m :=
    le_of_lt (probability_pos F β m)
  have hsq : 0 ≤ (F.charge m a - chargeMean F β a)^2 := sq_nonneg _
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
    mul_nonneg hprob hsq

theorem chargeCovariance_symm
    (F : Family ι) (β : Fin 2 → ℝ) (a b : Fin 2) :
    chargeCovariance F β a b = chargeCovariance F β b a := by
  unfold chargeCovariance
  apply Finset.sum_congr rfl
  intro m _hm
  ring

theorem chargeCovarianceMatrix_isSymm
    (F : Family ι) (β : Fin 2 → ℝ) :
    ∀ a b, chargeCovarianceMatrix F β a b =
      chargeCovarianceMatrix F β b a := by
  intro a b
  exact chargeCovariance_symm F β a b

theorem chargeCovariance_quadratic_eq_expect_sq
    (F : Family ι) (β v : Fin 2 → ℝ) :
    (∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovariance F β a b * v b) =
      ∑ m : ι, probability F β m *
        (∑ a : Fin 2, v a * centeredCharge F β m a) ^ (2 : ℕ) := by
  unfold chargeCovariance centeredCharge
  simp_rw [pow_two]
  calc
    (∑ a : Fin 2, ∑ b : Fin 2,
      v a * (∑ m : ι, probability F β m *
        (F.charge m a - chargeMean F β a) *
        (F.charge m b - chargeMean F β b)) * v b) =
      ∑ a : Fin 2, ∑ b : Fin 2, ∑ m : ι,
        probability F β m *
          (v a * (F.charge m a - chargeMean F β a)) *
          (v b * (F.charge m b - chargeMean F β b)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _hm
      ring
    _ = ∑ a : Fin 2, ∑ m : ι, ∑ b : Fin 2,
        probability F β m *
          (v a * (F.charge m a - chargeMean F β a)) *
          (v b * (F.charge m b - chargeMean F β b)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = ∑ m : ι, ∑ a : Fin 2, ∑ b : Fin 2,
        probability F β m *
          (v a * (F.charge m a - chargeMean F β a)) *
          (v b * (F.charge m b - chargeMean F β b)) := by
      rw [Finset.sum_comm]
    _ = ∑ m : ι, probability F β m *
        ((∑ a : Fin 2, v a * (F.charge m a - chargeMean F β a)) *
          (∑ a : Fin 2, v a * (F.charge m a - chargeMean F β a))) := by
      apply Finset.sum_congr rfl
      intro m _hm
      calc
        ∑ a : Fin 2, ∑ b : Fin 2,
            probability F β m *
              (v a * (F.charge m a - chargeMean F β a)) *
              (v b * (F.charge m b - chargeMean F β b)) =
            ∑ a : Fin 2,
              probability F β m *
                (v a * (F.charge m a - chargeMean F β a)) *
                (∑ b : Fin 2, v b * (F.charge m b - chargeMean F β b)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact (Finset.mul_sum (s := (Finset.univ : Finset (Fin 2)))
            (a := probability F β m *
              (v a * (F.charge m a - chargeMean F β a)))
            (f := fun b => v b * (F.charge m b - chargeMean F β b))).symm
        _ = ∑ a : Fin 2,
              probability F β m *
                ((∑ b : Fin 2, v b * (F.charge m b - chargeMean F β b)) *
                  (v a * (F.charge m a - chargeMean F β a))) := by
          apply Finset.sum_congr rfl
          intro a _ha
          ring
        _ = probability F β m *
              ((∑ b : Fin 2, v b * (F.charge m b - chargeMean F β b)) *
                (∑ b : Fin 2, v b * (F.charge m b - chargeMean F β b))) := by
          calc
            (∑ a : Fin 2, probability F β m *
                ((∑ b : Fin 2, v b *
                  (F.charge m b - chargeMean F β b)) *
                  (v a * (F.charge m a - chargeMean F β a)))) =
                probability F β m *
                  (∑ a : Fin 2,
                    (∑ b : Fin 2, v b *
                      (F.charge m b - chargeMean F β b)) *
                      (v a * (F.charge m a - chargeMean F β a))) := by
              exact (Finset.mul_sum (s := (Finset.univ : Finset (Fin 2)))
                (a := probability F β m)
                (f := fun a =>
                  (∑ b : Fin 2, v b *
                    (F.charge m b - chargeMean F β b)) *
                    (v a * (F.charge m a - chargeMean F β a)))).symm
            _ = probability F β m *
                ((∑ b : Fin 2, v b *
                    (F.charge m b - chargeMean F β b)) *
                  (∑ a : Fin 2, v a *
                    (F.charge m a - chargeMean F β a))) := by
              congr 1
              calc
                (∑ a : Fin 2,
                    (∑ b : Fin 2, v b *
                      (F.charge m b - chargeMean F β b)) *
                      (v a * (F.charge m a - chargeMean F β a))) =
                    ∑ a : Fin 2,
                      (v a * (F.charge m a - chargeMean F β a)) *
                        (∑ b : Fin 2, v b *
                          (F.charge m b - chargeMean F β b)) := by
                  apply Finset.sum_congr rfl
                  intro a _ha
                  ring
                _ = (∑ a : Fin 2, v a *
                    (F.charge m a - chargeMean F β a)) *
                      (∑ b : Fin 2, v b *
                        (F.charge m b - chargeMean F β b)) := by
                  rw [Finset.sum_mul]
            _ = probability F β m *
                ((∑ b : Fin 2, v b *
                  (F.charge m b - chargeMean F β b)) *
                  (∑ b : Fin 2, v b *
                    (F.charge m b - chargeMean F β b))) := by
              ring

theorem centeredCharge_mean_zero
    (F : Family ι) (β : Fin 2 → ℝ) (a : Fin 2) :
    ∑ m : ι, probability F β m * centeredCharge F β m a = 0 := by
  unfold centeredCharge chargeMean
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfactor :
      (∑ m, probability F β m * (∑ n, probability F β n * F.charge n a)) =
        (∑ m, probability F β m) *
          (∑ n, probability F β n * F.charge n a) := by
    rw [Finset.sum_mul]
  rw [hfactor, probability_sum_one]
  ring

theorem directionalCenteredCharge_mean_zero
    (F : Family ι) (β v : Fin 2 → ℝ) :
    ∑ m : ι, probability F β m * directionalCenteredCharge F β v m = 0 := by
  unfold directionalCenteredCharge
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _ha
  calc
    ∑ x : ι, probability F β x * (v a * centeredCharge F β x a) =
      v a * (∑ x : ι, probability F β x * centeredCharge F β x a) := by
        calc
          ∑ x : ι, probability F β x * (v a * centeredCharge F β x a) =
              ∑ x : ι, (probability F β x * centeredCharge F β x a) * v a := by
                apply Finset.sum_congr rfl
                intro x _hx
                ring
          _ = (∑ x : ι, probability F β x * centeredCharge F β x a) * v a := by
                rw [Finset.sum_mul]
          _ = v a * (∑ x : ι, probability F β x * centeredCharge F β x a) := by ring
    _ = 0 := by rw [centeredCharge_mean_zero]; ring

theorem covariance_quadratic_eq_zero_iff
    (F : Family ι) (β v : Fin 2 → ℝ) :
    (∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovariance F β a b * v b = 0) ↔
      ∀ m : ι, directionalCenteredCharge F β v m = 0 := by
  rw [chargeCovariance_quadratic_eq_expect_sq]
  constructor
  · intro h m
    have hnonneg : ∀ x : ι, 0 ≤ probability F β x *
        (directionalCenteredCharge F β v x) ^ (2 : ℕ) := by
      intro x
      exact mul_nonneg (le_of_lt (probability_pos F β x)) (sq_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _hx => hnonneg x)).mp h
    have hterm := hz m (Finset.mem_univ m)
    have hprob : probability F β m ≠ 0 := (probability_pos F β m).ne'
    have hsq : (directionalCenteredCharge F β v m) ^ (2 : ℕ) = 0 :=
      (mul_eq_zero.mp hterm).resolve_left hprob
    exact sq_eq_zero_iff.mp hsq
  · intro h
    apply Finset.sum_eq_zero
    intro m _hm
    change probability F β m * (directionalCenteredCharge F β v m) ^ (2 : ℕ) = 0
    rw [h m]
    simp

theorem covariance_quadratic_eq_zero_iff_charge_differences
    (F : Family ι) (β v : Fin 2 → ℝ) :
    (∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovariance F β a b * v b = 0) ↔
      ∀ m n : ι, ∑ a : Fin 2,
        v a * (F.charge m a - F.charge n a) = 0 := by
  constructor
  · intro h m n
    have hzm := (covariance_quadratic_eq_zero_iff F β v).mp h m
    have hzn := (covariance_quadratic_eq_zero_iff F β v).mp h n
    calc
      ∑ a : Fin 2, v a * (F.charge m a - F.charge n a) =
          directionalCenteredCharge F β v m -
            directionalCenteredCharge F β v n := by
              unfold directionalCenteredCharge centeredCharge
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro a _ha
              ring
      _ = 0 := by rw [hzm, hzn]; ring
  · intro h
    apply (covariance_quadratic_eq_zero_iff F β v).mpr
    classical
    let m₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    have hconst : ∀ m : ι,
        directionalCenteredCharge F β v m =
          directionalCenteredCharge F β v m₀ := by
      intro m
      unfold directionalCenteredCharge centeredCharge
      calc
        ∑ a : Fin 2, v a * (F.charge m a - chargeMean F β a) =
            (∑ a : Fin 2, v a *
              (F.charge m a - F.charge m₀ a)) +
              ∑ a : Fin 2, v a *
                (F.charge m₀ a - chargeMean F β a) := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro a _ha
                  ring
        _ = ∑ a : Fin 2, v a *
              (F.charge m₀ a - chargeMean F β a) := by
                rw [h m m₀]
                simp
    have hmean := directionalCenteredCharge_mean_zero F β v
    have hbase : directionalCenteredCharge F β v m₀ = 0 := by
      have hfactor :
          (∑ m : ι, probability F β m *
            directionalCenteredCharge F β v m) =
          directionalCenteredCharge F β v m₀ *
            (∑ m : ι, probability F β m) := by
        calc
          ∑ m : ι, probability F β m *
              directionalCenteredCharge F β v m =
            ∑ m : ι, directionalCenteredCharge F β v m₀ *
              probability F β m := by
                apply Finset.sum_congr rfl
                intro m _hm
                rw [hconst]
                ring
          _ = directionalCenteredCharge F β v m₀ *
              (∑ m : ι, probability F β m) := by
                rw [Finset.mul_sum]
      rw [hfactor, probability_sum_one] at hmean
      simpa using hmean
    intro m
    rw [hconst m, hbase]

theorem covariance_kernel_independent_of_beta
    (F : Family ι) (β₁ β₂ v : Fin 2 → ℝ) :
    (∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovariance F β₁ a b * v b = 0) ↔
    (∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovariance F β₂ a b * v b = 0) := by
  rw [covariance_quadratic_eq_zero_iff_charge_differences,
    covariance_quadratic_eq_zero_iff_charge_differences]

theorem chargeCovariance_posSemidefinite
    (F : Family ι) (β v : Fin 2 → ℝ) :
    0 ≤ ∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovariance F β a b * v b := by
  rw [chargeCovariance_quadratic_eq_expect_sq]
  apply Finset.sum_nonneg
  intro m _hm
  exact mul_nonneg (le_of_lt (probability_pos F β m)) (sq_nonneg _)

def ChargesSeparateDirections (F : Family ι) : Prop :=
  ∀ v : Fin 2 → ℝ, v ≠ 0 →
    ∃ m n : ι, ∑ a : Fin 2,
      v a * (F.charge m a - F.charge n a) ≠ 0

theorem chargeCovariance_posDef_of_separatesDirections
    (F : Family ι) (hF : ChargesSeparateDirections F)
    (β v : Fin 2 → ℝ) (hv : v ≠ 0) :
    0 < ∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovariance F β a b * v b := by
  have hnonneg := chargeCovariance_posSemidefinite F β v
  by_contra hnot
  have hzero : ∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovariance F β a b * v b = 0 :=
    le_antisymm (not_lt.mp hnot) hnonneg
  obtain ⟨m, n, hmn⟩ := hF v hv
  exact hmn ((covariance_quadratic_eq_zero_iff_charge_differences F β v).mp
    hzero m n)

theorem chargeCovarianceMatrix_posSemidefinite
    (F : Family ι) (β v : Fin 2 → ℝ) :
    0 ≤ ∑ a : Fin 2, ∑ b : Fin 2,
      v a * chargeCovarianceMatrix F β a b * v b := by
  exact chargeCovariance_posSemidefinite F β v

end InfoGeometry.Algebraic.CartanSouriauMassieu

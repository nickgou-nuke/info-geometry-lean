import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Analytic.LogSumExp
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Analytic
open scoped BigOperators

namespace InfoGeometry.Lie.CanonicalZornG2CartanMassieuStable

variable {State : Type*} [Fintype State] [Nonempty State]
  (D : CartanSouriauDatum State)

def potential (beta : Fin 2 → ℝ) : ℝ := Real.log (realGibbsPartition D beta)

def slice (beta : Fin 2 → ℝ) (i : Fin 2) (t : ℝ) : Fin 2 → ℝ :=
  fun j => if j = i then t else beta j

def meanCharge (beta : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  ∑ x : State, realGibbsWeight D beta x * D.momentMap x i

theorem slice_eq_logSumExp (beta : Fin 2 → ℝ) (i : Fin 2) (t : ℝ) :
    potential D (slice beta i t) =
      logSumExp (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) t := by
  unfold potential slice logSumExp logSumExpPartition realGibbsPartition
    realGibbsKernel realPairingEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [← Real.exp_add]
  congr 1
  simp only [Fin.sum_univ_two]
  fin_cases i <;> simp <;> ring

theorem partial_eq_logSumExpMean (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => potential D (slice beta i t)) (beta i) =
      logSumExpMean (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) (beta i) := by
  have hw : ∀ x, 0 < Real.exp
      (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)) :=
    fun x => Real.exp_pos _
  have hslice : (fun t => potential D (slice beta i t)) =
      fun t => logSumExp (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) t := by
    ext t
    exact slice_eq_logSumExp D beta i t
  rw [hslice, logSumExp_deriv_eq_mean _ _ hw]

theorem partial_eq_neg_meanCharge (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => potential D (slice beta i t)) (beta i) =
      -meanCharge D beta i := by
  rw [partial_eq_logSumExpMean D beta i]
  let w : State → ℝ := fun x => Real.exp
    (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j))
  let a : State → ℝ := fun x => -D.momentMap x i
  change logSumExpMean w a (beta i) = -meanCharge D beta i
  have hw : ∀ x, 0 < w x := by
    intro x
    exact Real.exp_pos _
  rw [logSumExpMean_eq_weighted_sum w a hw (beta i)]
  have hpart : logSumExpPartition w a (beta i) = realGibbsPartition D beta := by
    unfold logSumExpPartition realGibbsPartition w a realGibbsKernel
      realPairingEnergy
    apply Finset.sum_congr rfl
    intro x _
    rw [← Real.exp_add]
    congr 1
    simp only [w, a, realPairingEnergy, Fin.sum_univ_two]
    fin_cases i <;> simp <;> ring
  have hweight : ∀ x, logSumExpWeight w a (beta i) x =
      realGibbsWeight D beta x := by
    intro x
    unfold logSumExpWeight realGibbsWeight realGibbsKernel
    rw [hpart]
    rw [← Real.exp_add]
    congr 1
    simp only [w, a, realPairingEnergy, Fin.sum_univ_two]
    fin_cases i <;> simp <;> ring
  simp_rw [hweight]
  unfold meanCharge a
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]

theorem second_partial_eq_variance (beta : Fin 2 → ℝ) (i : Fin 2) :
    deriv (fun t => deriv (fun t' => potential D (slice beta i t')) t) (beta i) =
      logSumExpVariance (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) (beta i) := by
  have hw : ∀ x, 0 < Real.exp
      (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)) :=
    fun x => Real.exp_pos _
  have hslice : (fun t => potential D (slice beta i t)) =
      fun t => logSumExp (fun x => Real.exp
        (-(∑ j, if j = i then (0 : ℝ) else beta j * D.momentMap x j)))
        (fun x => -D.momentMap x i) t := by
    ext t
    exact slice_eq_logSumExp D beta i t
  rw [hslice]
  exact logSumExp_secondDeriv_eq_variance _ _ hw _

end InfoGeometry.Lie.CanonicalZornG2CartanMassieuStable

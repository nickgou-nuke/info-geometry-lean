import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

/--
`ExponentialFamily α θ` abstracts exponential families of probability
distributions on sample space `α` with parameter `θ`.
-/
class ExponentialFamily (α η : Type _) where
  statistic : α → η → ℝ
  logPartition : η → ℝ
  density : η → α → ℝ
  density_eq :
    ∀ p a,
      density p a =
        Real.exp (statistic a p - logPartition p)

/--
Finite exponential families with normalization.
-/
class FiniteExponentialFamily
    (α η : Type _)
    [Fintype α]
    extends ExponentialFamily α η where
  normalization :
    ∀ p, Finset.univ.sum (density p) = 1

namespace InfoGeometry.ExponentialFamily.Class

lemma density_pos
    {α η : Type _}
    [ExponentialFamily α η]
    (p : η) (a : α) :
    0 < ExponentialFamily.density p a := by
  rw [ExponentialFamily.density_eq]
  exact Real.exp_pos _

end InfoGeometry.ExponentialFamily.Class

/-!
## Multinomial Family
-/

noncomputable section
open Finset

variable {α : Type _} [Fintype α] [Nonempty α]

def multinomialStatistic
    (a : α) (p : α → ℝ) : ℝ :=
  p a

def multinomialLogPartition
    (p : α → ℝ) : ℝ :=
  Real.log (∑ b, Real.exp (p b))

def multinomialDensity
    (p : α → ℝ) (a : α) : ℝ :=
  Real.exp (p a)
    / (∑ b, Real.exp (p b))

lemma multinomial_partition_pos
    (p : α → ℝ) :
    0 < ∑ a, Real.exp (p a) := by
  classical
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset α))
      (f := fun a => Real.exp (p a))
      (by
        intro a ha
        exact Real.exp_pos _)
      Finset.univ_nonempty)

lemma multinomial_density_pos
    (p : α → ℝ) (a : α) :
    0 < multinomialDensity p a := by
  classical
  unfold multinomialDensity
  apply div_pos
  · exact Real.exp_pos _
  · exact multinomial_partition_pos p

lemma multinomial_density_eq
    (p : α → ℝ) (a : α) :
    multinomialDensity p a
      =
      Real.exp
        (multinomialStatistic a p
          - multinomialLogPartition p) := by
  unfold multinomialDensity multinomialStatistic multinomialLogPartition
  rw [Real.exp_sub]
  have hpos : 0 < ∑ b, Real.exp (p b) := multinomial_partition_pos p
  rw [Real.exp_log hpos]

lemma multinomial_normalization
    (p : α → ℝ) :
    ∑ a, multinomialDensity p a = 1 := by
  unfold multinomialDensity
  have hne : (∑ a, Real.exp (p a)) ≠ 0 := ne_of_gt (multinomial_partition_pos p)
  calc
    ∑ a, Real.exp (p a) / ∑ b, Real.exp (p b)
        = (∑ a, Real.exp (p a)) / ∑ b, Real.exp (p b) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset α))
                (f := fun a => Real.exp (p a))
                (a := ∑ b, Real.exp (p b)))
    _ = 1 := by
          exact div_self hne

/--
Multinomial exponential family instance.
-/
noncomputable instance
    MultinomialExponentialFamily :
    FiniteExponentialFamily α (α → ℝ) where
  statistic := multinomialStatistic
  logPartition := multinomialLogPartition
  density := multinomialDensity
  density_eq := multinomial_density_eq
  normalization := multinomial_normalization
